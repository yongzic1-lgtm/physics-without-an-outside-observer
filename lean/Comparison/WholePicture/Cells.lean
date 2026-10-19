module

public import Comparison.WholePicture.Spectra
public import Comparison.Existence.Plaquette

/-!
# The whole picture, statement 6: the cells of RP⁴ and the flux around the squares

The two-spinor states and their steps are the cells of the
five-cube with the whole flip: sixteen vertices (`Fin 16`), forty links (`linkU`, `linkV` of `PlaquetteData`, each along `linkLine`), forty squares (`sqX`, `sqS`, `sqT`), twenty cubes (`cubeX`,
three lines `cubeA < cubeB < cubeD`) and five four-cells (all sixteen vertices, the four lines other
than `j`). `links_complete`, `links_distinct`, `squares_complete`, `squares_distinct` stand in
`PlaquetteData.lean`; here:

* `cubes_complete`, `cubes_distinct`, `card_cubeSet`: **the twenty cubes**, each of eight vertices,
  every cube `x + ⟨g_a, g_b, g_d⟩` once; `euler_number`: `16 − 40 + 40 − 20 + 5 = 1`.
* `bd1`, …, `bd4`: the boundaries mod 2 (a plane lies in a cell when its vertices and lines do);
  `bd_bd`: **the boundary of a boundary is nothing**; `rank_bd1` … `rank_bd4`: ranks `15, 24, 15, 4`
  over `ZMod 2` (certificates: an invertible minor and a factorization); `homology_mod_two`:
  **one class in each dimension mod 2**, `dim(ker ∂_k / im ∂_{k+1}) = 1` for `k = 0, …, 4`.
* `cReal`: the circulation matrix `C` (squares × links, `cZ`) over `ℝ`; `C · grad = 0` is
  `cZ_div` (`PlaquetteData.lean`); `rank_cReal`: **`rank C = 25`**; `cReal_gram_charpoly`:
  **`det(X − CᵀC) = X¹⁵ (X − 4)¹⁰ (X − 8)¹⁵`**, i.e. `spec CᵀC = 0¹⁵ ⊕ 4¹⁰ ⊕ 8¹⁵`.
-/

@[expose] public section

namespace Comparison.WholePicture

open Matrix Polynomial

/-! ## Certificates for ranks -/

/-- **A rank from a certificate:** an invertible `r × r` minor and a factorization through `r`
columns give `rank M = r`. -/
theorem rank_eq_of_cert {m n : Type*} [Finite m] [Fintype n] {K : Type*} [Field K]
    (M : Matrix m n K) {r : ℕ} (R : Fin r → m) (Cc : Fin r → n)
    (Q : Matrix (Fin r) (Fin r) K) (Y : Matrix (Fin r) n K)
    (hQ : M.submatrix R Cc * Q = 1) (hY : M = M.submatrix id Cc * Y) : M.rank = r := by
  classical
  have := Fintype.ofFinite m
  apply le_antisymm
  · calc M.rank = (M.submatrix id Cc * Y).rank := by rw [← hY]
      _ ≤ (M.submatrix id Cc).rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin r) := Matrix.rank_le_card_width _
      _ = r := Fintype.card_fin r
  · have hu : IsUnit (M.submatrix R Cc) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse hQ)
    calc r = (M.submatrix R Cc).rank := by rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
      _ ≤ M.rank := Matrix.rank_submatrix_le _ _ _

/-- **One class:** if `f g = 0` and `dim b = rank f + rank g + 1`, then `ker f / im g` is
one-dimensional. -/
theorem homology_finrank_one {K : Type*} [Field K] {a b c : Type*} [Fintype b] [Fintype c]
    (f : Matrix a b K) (g : Matrix b c K)
    (hfg : f * g = 0) (h : Fintype.card b = f.rank + g.rank + 1) :
    Module.finrank K (LinearMap.ker f.mulVecLin ⧸
      (LinearMap.range g.mulVecLin).comap (LinearMap.ker f.mulVecLin).subtype) = 1 := by
  have hle : LinearMap.range g.mulVecLin ≤ LinearMap.ker f.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hfg, Matrix.zero_mulVec]
  have h1 := Submodule.finrank_quotient_add_finrank
    ((LinearMap.range g.mulVecLin).comap (LinearMap.ker f.mulVecLin).subtype)
  have h2 : Module.finrank K ((LinearMap.range g.mulVecLin).comap
      (LinearMap.ker f.mulVecLin).subtype) = g.rank :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)
  have h3 := LinearMap.finrank_range_add_finrank_ker f.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h3
  have h4 : f.rank = Module.finrank K (LinearMap.range f.mulVecLin) := rfl
  omega

/-! ## The tables -/

def linkLine : Fin 40 → Fin 5 :=
  ![0, 1, 2, 3, 4, 1, 2, 3, 4, 0, 2, 3, 4, 0, 1, 3, 4, 0, 1, 2, 4, 0, 1, 2, 3, 4, 3, 2, 4, 3, 1, 4,
    2, 1, 3, 2, 1, 0, 0, 0]

def cubeX : Fin 20 → Fin 16 :=
  ![0, 4, 0, 3, 0, 3, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1]

def cubeA : Fin 20 → Fin 5 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]

def cubeB : Fin 20 → Fin 5 :=
  ![1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 2, 2, 3, 3, 3, 3]

def cubeD : Fin 20 → Fin 5 :=
  ![2, 2, 3, 3, 4, 4, 3, 3, 4, 4, 4, 4, 3, 3, 4, 4, 4, 4, 4, 4]

def bd1Rows : Fin 15 → Fin 16 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

def bd1Cols : Fin 15 → Fin 40 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 15, 16, 20]

def bd1Q : Matrix (Fin 15) (Fin 15) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def bd1Y : Matrix (Fin 15) (Fin 40) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1,
    1, 0, 1, 1, 0, 1, 1, 1;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0,
    0, 1, 0, 0, 1, 0, 1, 1;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 1, 0, 0]

def bd2Rows : Fin 24 → Fin 40 :=
  ![0, 1, 2, 3, 5, 6, 7, 9, 10, 11, 13, 14, 15, 17, 18, 19, 21, 22, 23, 25, 26, 28, 29, 32]

def bd2Cols : Fin 24 → Fin 40 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 23, 24, 30]

def bd2Q : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0;
    1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1;
    0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0;
    0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0]

def bd2Y : Matrix (Fin 24) (Fin 40) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0,
    1, 1, 0, 1, 0, 0, 1, 1, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0,
    1, 1, 0, 0, 1, 0, 1, 1;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1,
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1,
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
    1, 0, 0, 1, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1,
    1, 0, 0, 0, 1, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1,
    0, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1,
    1, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1,
    0, 1, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    1, 1, 0, 0, 1, 0, 1, 1]

def bd3Rows : Fin 15 → Fin 40 :=
  ![0, 1, 2, 4, 5, 7, 10, 11, 13, 16, 17, 19, 22, 23, 28]

def bd3Cols : Fin 15 → Fin 20 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16]

def bd3Q : Matrix (Fin 15) (Fin 15) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0;
    1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0]

def bd3Y : Matrix (Fin 15) (Fin 20) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1]

def bd4Rows : Fin 4 → Fin 20 :=
  ![0, 2, 6, 12]

def bd4Cols : Fin 4 → Fin 5 :=
  ![0, 1, 2, 3]

def bd4Q : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1;
    0, 0, 1, 0;
    0, 1, 0, 0;
    1, 0, 0, 0]

def bd4Y : Matrix (Fin 4) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 1;
    0, 1, 0, 0, 1;
    0, 0, 1, 0, 1;
    0, 0, 0, 1, 1]

def cRows : Fin 25 → Fin 40 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 23, 24, 25, 30]

def cCols : Fin 25 → Fin 40 :=
  ![0, 1, 2, 3, 5, 6, 7, 9, 10, 11, 13, 14, 15, 17, 18, 19, 21, 22, 23, 25, 26, 28, 29, 31, 32]

def cInv2 : Matrix (Fin 25) (Fin 25) ℤ :=
  !![0, 0, -2, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2;
    2, 0, -2, 0, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, -2;
    0, 2, -2, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 2, 0, -2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, -2, 0, 1, 0, -1, 1, 0, -1, 0;
    -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0, -1, -1, 0, -1, -2, 0, 1, 0, -1, 1, 0, -1, 0;
    -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 2, -1, -1, 0, -1, 0, -2, 1, 2, -1, 1, 0, -1, 0;
    -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, -2, 0, -1, 0, -1, 1, 0, -1, 0;
    -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 0, 0, -1, 0, -1, 1, 0, -1, 0;
    -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 0, 0, -1, 2, -1, 1, 0, -1, 0;
    -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0, -1, -1, 2, -1, -2, 0, 1, 0, -1, 1, -2, -1, 0;
    1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, -1, 2, -1, 0, 0, 1, 0, -1, 1, -2, -1, 0;
    1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, -1, 2, -1, 0, 0, 1, 0, -1, 1, -2, 1, 0;
    -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 2, -1, -1, 0, 1, 0, -2, 1, 2, -1, 1, 0, -1, -2;
    1, 1, -2, 0, -1, 2, 0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 1, 2, -1, 1, 0, -1, -2;
    1, 1, -2, 0, 1, 0, 0, 2, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 1, 0, -1, 1, 0, 1, -2;
    0, 0, -2, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2;
    2, 0, -2, 0, 0, 0, 2, 0, 0, -2, 0, 0, -2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, -2;
    0, 2, -2, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 2, 0, -2;
    1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 1, 2, 0, -1, 0, 1, -1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 2, 0, 0, 0, 0, 0;
    1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 1, 1, -2, 1, 2, 0, -1, 0, 1, -1, 0, 1, 0;
    2, -2, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, -2, 0, 2, 0;
    1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -2, 1, 1, 0, -1, 0, 2, -1, -2, 1, -1, 0, 1, 0;
    2, -2, 0, 0, 2, 0, 0, 0, 0, 0, 0, -2, 0, 2, 0, 0, 0, 2, 0, -2, 0, -2, 0, 2, 0]

def cY : Matrix (Fin 25) (Fin 40) ℤ :=
  !![1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 1, 0, 0;
    0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, -1, 1, 0, 1;
    0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, -1, 0, 1, -1, 0;
    0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, -1, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, -1, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 0, -1, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, -1, 0, 1, -1, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, -1, 0, 1, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, -1, 1, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, -1, 1, 0, -1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, -1, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, -1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 1, -1, 0, 1, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, -1, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, -1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, -1, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, -1, 0, 1, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
    0, 0, 0, 1, 0, -1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0,
    0, 0, 0, 1, -1, 0, 1, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1,
    0, 0, 0, 1, -1, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
    0, 0, 0, 1, 0, -1, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0, -1, -1, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, -1, 0, 1, -1, 0, 1, 1]

def gTab : Fin 40 → Fin 40 → ℤ :=
  ![![4, -1, -1, -1, -1, 1, 1, 1, 1, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 4, -1, -1, -1, -1, 0, 0, 0, 1, 1, 1, 1, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, -1, 4, -1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 1, 1, 1, 1, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, -1, -1, 4, -1, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 1, 1, 1, 0, 0, 0, -1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, -1, -1, -1, 4, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 1, 1, 1, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, -1, 0, 0, 0, 4, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0,
      0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0],
    ![1, 0, -1, 0, 0, -1, 4, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      1, 1, 0, -1, 0, 0, -1, 0, 0, 0, 0],
    ![1, 0, 0, -1, 0, -1, -1, 4, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      -1, 0, 1, 1, 1, -1, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, -1, -1, -1, -1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, -1,
      0, 0, -1, 0, 0, 1, 1, 1, 0, 0, 0],
    ![-1, 1, 0, 0, 0, -1, 0, 0, 0, 4, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1],
    ![0, 1, -1, 0, 0, 0, 0, 0, 0, -1, 4, -1, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0,
      0, 0, -1, 1, 0, -1, 1, 0, 1, 0, 0],
    ![0, 1, 0, -1, 0, 0, 0, 0, 0, -1, -1, 4, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1,
      1, 0, 0, 0, 0, 1, -1, 0, 0, 1, 0],
    ![0, 1, 0, 0, -1, 0, 0, 0, 0, -1, -1, -1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 1,
      -1, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1],
    ![-1, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 4, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      1, 1, 0, 0, 0, 0, 0, 0, -1, 1, 1],
    ![0, -1, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 4, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1, -1, 0, 1, -1, 0, 1, 1, 0, 0],
    ![0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 4, -1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 1, 0, 0,
      -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1],
    ![0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 4, 0, 0, 0, 0, 0, 0, -1, 0, 1, -1, 0, -1,
      0, 0, 1, 0, -1, 0, 0, 0, 0, -1, 0],
    ![-1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 1, 1, 0, 0, 0, 1, -1, 1],
    ![0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 4, -1, -1, 0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, -1, 0, -1, 1, 0, 1, 0],
    ![0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, 4, -1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0, 0, -1, 0, 0, 1, -1, 0, 0, -1],
    ![0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 4, 0, 0, 0, -1, 1, 0, -1, 1,
      0, -1, -1, 0, 0, 0, 0, 0, -1, 0, 0],
    ![-1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, -1, -1, -1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 1, 1, 1, 1, -1],
    ![0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 4, -1, -1, 0, 0, 0, 0,
      -1, 1, 0, -1, 1, 0, 0, -1, 0, 0, 1],
    ![0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, -1, 4, -1, 0, -1, 1, 0,
      0, 0, 0, 1, -1, 0, -1, 0, 0, -1, 0],
    ![0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, 4, 0, 1, -1, 0,
      1, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, -1, 1, 0, 0, -1, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0, 0, 0, 4, -1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1],
    ![0, 0, 0, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, 1, -1, 4, -1, 0,
      0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 1, -1, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1, -1, -1, -1, 4, 0,
      0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1, 1, 1, 0, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4,
      -1, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, -1, 1, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, -1,
      4, -1, 0, -1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 0, -1, -1,
      -1, 4, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 0, 1, 0, -1, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 4, -1, -1, -1, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      -1, 0, -1, 4, -1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 1, -1, 0, 0, 0, 1, -1, 0, 0, -1, 0, 0,
      0, 0, -1, -1, 4, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1, 1, 0, -1, 1, 0, 0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0,
      0, -1, 0, 0, 4, -1, -1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, 1, 0, 1, 0, -1, 0, 0, 0, 0, -1,
      0, 0, 0, 0, 0, -1, 4, -1, 0, 1, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1, -1, 0, 1, -1, 0, 0, -1, 0, 0, 0,
      0, 0, 0, 0, 0, -1, -1, 4, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0, 1, 0, 0, -1, 1, 0, 0, -1, 0, 0, -1, 0,
      0, -1, 1, 0, 0, 1, 0, 0, 4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 1, 0, 0, -1, -1, 1, 0, 0, 1, 0, -1, 0, 0, -1, 0, 1,
      0, 0, 0, 0, -1, 0, 1, 0, 0, 4, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, -1, 0, 1, 0, -1, 0, -1, 1, 0, 0, -1, 0, 0, 0,
      1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 4]]

/-! ## The cells -/

theorem linkLine_spec : ∀ l : Fin 40, transition (linkLine l) (linkU l) = linkV l := by decide

/-- The four vertices of a square. -/
def sqSet (q : Fin 40) : Finset (Fin 16) := {sqVert q 0, sqVert q 1, sqVert q 2, sqVert q 3}

/-- The cube spanned at `x` by three lines: the eight vertices reached by transitions along them. -/
def cubeOf (x : Fin 16) (a b d : Fin 5) : Finset (Fin 16) :=
  {x, transition a x, transition b x, transition d x, transition a (transition b x), transition a (transition d x), transition b (transition d x),
    transition a (transition b (transition d x))}

/-- The vertices of the cube `c`. -/
def cubeSet (c : Fin 20) : Finset (Fin 16) := cubeOf (cubeX c) (cubeA c) (cubeB c) (cubeD c)

/-- The three lines of the cube `c`. -/
def cubeLines (c : Fin 20) : Finset (Fin 5) := {cubeA c, cubeB c, cubeD c}

/-- **The twenty cubes:** every cube of the five-cube with the whole flip appears. -/
theorem cubes_complete : ∀ (x : Fin 16) (a b d : Fin 5), a < b → b < d →
    ∃ c : Fin 20, cubeSet c = cubeOf x a b d ∧ cubeA c = a ∧ cubeB c = b ∧ cubeD c = d := by
  decide +kernel

/-- **…and each once.** -/
theorem cubes_distinct : ∀ c c' : Fin 20, cubeSet c = cubeSet c' → cubeA c = cubeA c' →
    cubeB c = cubeB c' → cubeD c = cubeD c' → c = c' := by
  decide +kernel

theorem cubes_ordered : ∀ c : Fin 20, cubeA c < cubeB c ∧ cubeB c < cubeD c := by decide

theorem card_cubeSet : ∀ c : Fin 20, (cubeSet c).card = 8 := by decide

theorem card_sqSet : ∀ q : Fin 40, (sqSet q).card = 4 := by decide

/-- **The Euler number of the cells is one:** `16 − 40 + 40 − 20 + 5 = 1`. -/
theorem euler_number : (16 : ℤ) - 40 + 40 - 20 + 5 = 1 := by norm_num

/-! ## The boundaries mod 2 -/

/-- `∂₁`: the two ends of a link. -/
def bd1 : Matrix (Fin 16) (Fin 40) (ZMod 2) :=
  Matrix.of fun v l => if v = linkU l ∨ v = linkV l then 1 else 0

/-- `∂₂`: the four links of a square. -/
def bd2 : Matrix (Fin 40) (Fin 40) (ZMod 2) :=
  Matrix.of fun l q =>
    if linkU l ∈ sqSet q ∧ linkV l ∈ sqSet q ∧
        (linkLine l = sqS q ∨ linkLine l = sqT q) then 1 else 0

/-- `∂₃`: the six squares of a cube. -/
def bd3 : Matrix (Fin 40) (Fin 20) (ZMod 2) :=
  Matrix.of fun q c =>
    if sqSet q ⊆ cubeSet c ∧ sqS q ∈ cubeLines c ∧ sqT q ∈ cubeLines c then 1 else 0

/-- `∂₄`: the eight cubes of a four-cell (the four-cell `j` holds the four lines other than `j`). -/
def bd4 : Matrix (Fin 20) (Fin 5) (ZMod 2) := Matrix.of fun c j => if j ∉ cubeLines c then 1 else 0

theorem bd1_bd2 : bd1 * bd2 = 0 := by decide +kernel
theorem bd2_bd3 : bd2 * bd3 = 0 := by decide +kernel
theorem bd3_bd4 : bd3 * bd4 = 0 := by decide +kernel

/-- **The boundary of a boundary is nothing.** -/
theorem bd_bd : bd1 * bd2 = 0 ∧ bd2 * bd3 = 0 ∧ bd3 * bd4 = 0 := ⟨bd1_bd2, bd2_bd3, bd3_bd4⟩

/-- Every link has two ends, every square four links, every cube six squares, every four-cell
eight cubes. -/
theorem bd_columns :
    (∀ l, ∑ v, bd1 v l = 0) ∧ (∀ q, (Finset.univ.filter fun l => bd2 l q = 1).card = 4) ∧
    (∀ c, (Finset.univ.filter fun q => bd3 q c = 1).card = 6) ∧
    (∀ j, (Finset.univ.filter fun c => bd4 c j = 1).card = 8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem bd1_cert : bd1.submatrix bd1Rows bd1Cols * bd1Q = 1 ∧
    bd1 = bd1.submatrix id bd1Cols * bd1Y := by
  constructor <;> decide +kernel

theorem bd2_cert : bd2.submatrix bd2Rows bd2Cols * bd2Q = 1 ∧
    bd2 = bd2.submatrix id bd2Cols * bd2Y := by
  constructor <;> decide +kernel

theorem bd3_cert : bd3.submatrix bd3Rows bd3Cols * bd3Q = 1 ∧
    bd3 = bd3.submatrix id bd3Cols * bd3Y := by
  constructor <;> decide +kernel

theorem bd4_cert : bd4.submatrix bd4Rows bd4Cols * bd4Q = 1 ∧
    bd4 = bd4.submatrix id bd4Cols * bd4Y := by
  constructor <;> decide +kernel

theorem rank_bd1 : bd1.rank = 15 := rank_eq_of_cert _ _ _ _ _ bd1_cert.1 bd1_cert.2
theorem rank_bd2 : bd2.rank = 24 := rank_eq_of_cert _ _ _ _ _ bd2_cert.1 bd2_cert.2
theorem rank_bd3 : bd3.rank = 15 := rank_eq_of_cert _ _ _ _ _ bd3_cert.1 bd3_cert.2
theorem rank_bd4 : bd4.rank = 4 := rank_eq_of_cert _ _ _ _ _ bd4_cert.1 bd4_cert.2

/-- **One class in each dimension mod 2:** `dim(ker ∂_k / im ∂_{k+1}) = 1` for `k = 0, 1, 2, 3, 4`
(`∂₀ = 0` on the vertices and `∂₅ = 0` into the four-cells). -/
theorem homology_mod_two :
    Module.finrank (ZMod 2) (LinearMap.ker (0 : Matrix (Fin 0) (Fin 16) (ZMod 2)).mulVecLin ⧸
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
        (LinearMap.ker bd4.mulVecLin).subtype) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact homology_finrank_one _ _ (by simp) (by rw [Matrix.rank_zero, rank_bd1]; simp)
  · exact homology_finrank_one _ _ bd1_bd2 (by rw [rank_bd1, rank_bd2]; simp)
  · exact homology_finrank_one _ _ bd2_bd3 (by rw [rank_bd2, rank_bd3]; simp)
  · exact homology_finrank_one _ _ bd3_bd4 (by rw [rank_bd3, rank_bd4]; simp)
  · exact homology_finrank_one _ _ (by simp) (by rw [rank_bd4, Matrix.rank_zero]; simp)

/-! ## The flux around the squares -/

/-- The circulation matrix `C` over `ℤ`: squares × links. -/
def cMat : Matrix (Fin 40) (Fin 40) ℤ := Matrix.of fun q l => cZ q l

theorem cMat_cert : cMat.submatrix cRows cCols * cInv2 = Matrix.diagonal (fun _ => (2 : ℤ)) ∧
    cMat = cMat.submatrix id cCols * cY := by
  constructor <;> decide +kernel

/-- `C` over `ℝ`. -/
noncomputable def cReal : Matrix (Fin 40) (Fin 40) ℝ := cMat.map (Int.castRingHom ℝ)

/-- **`rank C = 25 = 40 − 16 + 1`.** -/
theorem rank_cReal : cReal.rank = 25 := by
  refine rank_eq_of_cert cReal cRows cCols ((1 / 2 : ℝ) • cInv2.map (Int.castRingHom ℝ))
    (cY.map (Int.castRingHom ℝ)) ?_ ?_
  · have h := congrArg (fun M => M.map (Int.castRingHom ℝ)) cMat_cert.1
    simp only [Matrix.map_mul] at h
    rw [cReal, Matrix.submatrix_map, Matrix.mul_smul, h, Matrix.diagonal_map (map_zero _)]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  · have h := congrArg (fun M => M.map (Int.castRingHom ℝ)) cMat_cert.2
    simp only [Matrix.map_mul] at h
    rw [cReal, Matrix.submatrix_map]
    exact h

theorem gTab_eq : ∀ l m : Fin 40, GZ l m = gTab l m := by decide +kernel

/-- `CᵀC` over `ℤ`, as a table. -/
def gMat : Matrix (Fin 40) (Fin 40) ℤ := Matrix.of gTab

theorem gMat_cubic : gMat * gMat * gMat + (-12 : ℤ) • (gMat * gMat) + (32 : ℤ) • gMat = 0 := by
  decide +kernel

theorem gMat_trace : gMat.trace = 160 := by decide +kernel

theorem cReal_gram : cRealᵀ * cReal = gMat.map (Int.castRingHom ℝ) := by
  ext l m
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cReal, cMat, Matrix.map_apply,
    Matrix.of_apply, gMat, ← gTab_eq, GZ, eq_intCast]
  push_cast
  rfl

theorem cReal_gram_symm : (cRealᵀ * cReal).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- **`spec CᵀC = 0¹⁵ ⊕ 4¹⁰ ⊕ 8¹⁵`:** `det(X − CᵀC) = X¹⁵ (X − 4)¹⁰ (X − 8)¹⁵`. -/
theorem cReal_gram_charpoly :
    (cRealᵀ * cReal).charpoly = X ^ 15 * (X - C (4 : ℝ)) ^ 10 * (X - C (8 : ℝ)) ^ 15 := by
  set hA := cReal_gram_symm
  have hcub : (cRealᵀ * cReal) * (cRealᵀ * cReal) * (cRealᵀ * cReal) +
      (-12 : ℝ) • ((cRealᵀ * cReal) * (cRealᵀ * cReal)) + (32 : ℝ) • (cRealᵀ * cReal) +
      (0 : ℝ) • (1 : Matrix (Fin 40) (Fin 40) ℝ) = 0 := by
    have h := congrArg (Int.castRingHom ℝ).mapMatrix gMat_cubic
    simp only [map_add, map_mul, map_zsmul, map_zero, RingHom.mapMatrix_apply, ← cReal_gram] at h
    rw [zero_smul, add_zero, ← h]
    module
  have hroot := eig_root_cubic hA (-12) 32 0 hcub
  have hs : ∀ i, hA.eigenvalues i ∈ ({0, 4, 8} : Finset ℝ) := by
    intro i
    have h := hroot i
    have : hA.eigenvalues i * ((hA.eigenvalues i - 4) * (hA.eigenvalues i - 8)) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · simp [h1]
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · simp [sub_eq_zero.mp h2]
      · simp [sub_eq_zero.mp h2]
  have hcard := card_of_values hA _ hs
  have htr := trace_of_values hA _ hs
  have hrank := rank_of_values hA _ hs
  have htrace : (cRealᵀ * cReal).trace = 160 := by
    rw [cReal_gram]
    have h := gMat_trace
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, gMat, Matrix.of_apply] at h ⊢
    rw [← map_sum, h]
    norm_num
  rw [htrace] at htr
  rw [Matrix.rank_transpose_mul_self, rank_cReal] at hrank
  have h48 : (0 : ℝ) ∉ ({4, 8} : Finset ℝ) := by norm_num
  have h4 : (4 : ℝ) ≠ 8 := by norm_num
  rw [Finset.erase_insert h48, Finset.sum_pair h4] at hrank
  rw [Finset.sum_insert h48, Finset.sum_pair h4] at hcard htr
  rw [charpoly_of_values hA _ hs, Finset.prod_insert h48, Finset.prod_pair h4]
  simp only [Fintype.card_fin] at hcard
  set n0 := (Finset.univ.filter fun i => hA.eigenvalues i = 0).card
  set n4 := (Finset.univ.filter fun i => hA.eigenvalues i = 4).card
  set n8 := (Finset.univ.filter fun i => hA.eigenvalues i = 8).card
  have e8 : n8 = 15 := by
    have : (n4 : ℝ) + n8 = 25 := by exact_mod_cast hrank.symm
    have : (n8 : ℝ) = 15 := by linarith
    exact_mod_cast this
  have e4 : n4 = 10 := by omega
  have e0 : n0 = 15 := by omega
  rw [e0, e4, e8]
  simp only [map_zero, sub_zero]
  ring

end Comparison.WholePicture

end
