module

public import Comparison.Existence.Walk
public import Comparison.Elements.SixDirections

/-!
# Book X. The law: the Ihara–Bass factorization for the sixteen two-spinor states (Propositions 54, 56)

**The step of a line for five involutions.** For five operators `Γ_t` on a space `V` with
`Γ_t² = 1`, the step on `V ⊗ ℂ⁵` is `B(x ⊗ e_t) = Σ_{t' ≠ t} Γ_{t'} x ⊗ e_{t'}` (`stepOp`): the four
continuations, never the undo. On the sixteen two-spinor states with `Γ_t` the transitions of Proposition 14 it is
the matrix `B` of Proposition 26 on the eighty states; with `Γ_t = γ_t ⊗ 1` it is `B` carrying the
sign of each step (Proposition 30).

* `det_sylvester`: `c^{|W|} det(c − ZY) = c^{|N|} det(c − YZ)` over any commutative ring.
* `ihara_bass`: `(1 − u²)^{|V|} ∏_t det(1 − uΓ_t) · det(1 − uB) =
  (1 − u²)^{5|V|} det((1 + 4u²) − u Σ_t Γ_t)`, for every `u` in any commutative ring.
* `D_plus`: on the sixteen two-spinor states, for every `u : ℂ`,
  `det(1 − uB₊) = (1 − u²)²⁴ (1 − u)(1 − 4u)(1 − u + 4u²)¹⁰(1 + 3u + 4u²)⁵`
  (through the character table: `charTable_mul_self`, `transitionMat_mul_charTable`, the adjacency
  `adjacency_mul_charTable` with eigenvalues `5 − 2|T| = 5, 1, −3`).
* `D_minus`: with the sign of each step, `Γ_t = γ_t ⊗ 1`, `A₋² = 5` (`Aminus_sq`), for every `u : ℂ`,
  `det(1 − uB₋) = (1 − u²)²⁴ (1 + 3u² + 16u⁴)⁸`.
* `D_plus_opposite`: `D₊(u) D₊(−u) = (1 − u²)⁴⁹ (1 − 16u²)(1 + 7u² + 16u⁴)¹⁰(1 − u² + 16u⁴)⁵`.
* `D_plus_quarter`, `D_minus_quarter`: at `u = 1/4` only the factor `1 − 4u` of `D₊` vanishes.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-! ## A determinant identity -/

section General

variable {R : Type*} [CommRing R]

/-- **`c^{|W|} det(c·1 − Z Y) = c^{|N|} det(c·1 − Y Z)`** for rectangular `Z, Y`. -/
theorem det_sylvester {N W : Type*} [Fintype N] [DecidableEq N] [Fintype W] [DecidableEq W]
    (c : R) (Z : Matrix N W R) (Y : Matrix W N R) :
    c ^ Fintype.card W * (c • (1 : Matrix N N R) - Z * Y).det =
      c ^ Fintype.card N * (c • (1 : Matrix W W R) - Y * Z).det := by
  have hM : (fromBlocks (c • (1 : Matrix N N R)) Z Y (1 : Matrix W W R)).det =
      (c • (1 : Matrix N N R) - Z * Y).det := det_fromBlocks_one₂₂ _ _ _
  have hL : (fromBlocks (1 : Matrix N N R) 0 (-Y) (c • (1 : Matrix W W R))).det =
      c ^ Fintype.card W := by
    rw [det_fromBlocks_zero₁₂, det_one, one_mul, det_smul, det_one, mul_one]
  have hLM : fromBlocks (1 : Matrix N N R) 0 (-Y) (c • (1 : Matrix W W R)) *
      fromBlocks (c • (1 : Matrix N N R)) Z Y (1 : Matrix W W R) =
      fromBlocks (c • (1 : Matrix N N R)) Z 0 (c • (1 : Matrix W W R) - Y * Z) := by
    rw [fromBlocks_multiply]
    congr 1
    · rw [Matrix.one_mul, Matrix.zero_mul, add_zero]
    · rw [Matrix.one_mul, Matrix.zero_mul, add_zero]
    · rw [Matrix.neg_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
        neg_add_cancel]
    · simp only [Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one]
      abel
  have h := congrArg Matrix.det hLM
  rw [det_mul, hL, hM, det_fromBlocks_zero₂₁, det_smul, det_one, mul_one] at h
  exact h

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The step of a line for five involutions:** `B(x ⊗ e_t) = Σ_{t' ≠ t} Γ_{t'} x ⊗ e_{t'}`;
entry `((x', t'), (y, t))` is `Γ_{t'}(x', y)` when `t' ≠ t` and zero for the undo. -/
def stepOp (Γ : Fin 5 → Matrix V V R) : Matrix (V × Fin 5) (V × Fin 5) R :=
  Matrix.of fun p q => if p.2 = q.2 then 0 else Γ p.2 p.1 q.1

/-- The column of copies, `x ↦ Σ_t x ⊗ e_t`. -/
def colX (V' : Type*) [DecidableEq V'] (R' : Type*) [CommRing R'] : Matrix (V' × Fin 5) V' R' :=
  Matrix.of fun p y => if p.1 = y then 1 else 0

/-- The row of copies, `x ⊗ e_t ↦ x`. -/
def rowY (V' : Type*) [DecidableEq V'] (R' : Type*) [CommRing R'] : Matrix V' (V' × Fin 5) R' :=
  Matrix.of fun x q => if x = q.1 then 1 else 0

theorem colX_mul_rowY :
    colX V R * rowY V R = Matrix.of fun p q => if p.1 = q.1 then (1 : R) else 0 := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [colX, rowY, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single p.1]
  · by_cases h : p.1 = q.1 <;> simp [h]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem rowY_mul_colX : rowY V R * colX V R = (5 : R) • (1 : Matrix V V R) := by
  ext x y
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [colX, rowY, Matrix.of_apply, mul_ite, mul_one, mul_zero, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single x]
  · by_cases h : x = y <;> simp [h]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem blockDiagonal_mul_colX_rowY (Γ : Fin 5 → Matrix V V R) :
    blockDiagonal Γ * (colX V R * rowY V R) = Matrix.of fun p q => Γ p.2 p.1 q.1 := by
  rw [colX_mul_rowY]
  ext ⟨x', t'⟩ ⟨y, t⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.of_apply, blockDiagonal_apply, ite_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single t']
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [hb]
  · simp

theorem stepOp_eq (Γ : Fin 5 → Matrix V V R) :
    stepOp Γ = blockDiagonal Γ * (colX V R * rowY V R) - blockDiagonal Γ := by
  rw [blockDiagonal_mul_colX_rowY]
  ext ⟨x', t'⟩ ⟨y, t⟩
  simp only [stepOp, Matrix.of_apply, Matrix.sub_apply, blockDiagonal_apply]
  by_cases h : t' = t
  · subst h
    simp
  · simp [h]

theorem rowY_blockDiagonal_colX (Γ : Fin 5 → Matrix V V R) :
    rowY V R * blockDiagonal Γ * colX V R = ∑ t, Γ t := by
  ext x y
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, rowY, colX, Matrix.of_apply,
    blockDiagonal_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single y]
  · simp only [↓reduceIte]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single t]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun s _ => ?_
      simp [Ne.symm hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [hb]
  · simp

/-- **The Ihara–Bass factorization for five involutions:** for every `u`,
`(1 − u²)^{|V|} ∏_t det(1 − uΓ_t) · det(1 − uB) = (1 − u²)^{5|V|} det((1 + 4u²) − u Σ_t Γ_t)`. -/
theorem ihara_bass (Γ : Fin 5 → Matrix V V R) (hΓ : ∀ t, Γ t * Γ t = 1) (u : R) :
    (1 - u ^ 2) ^ Fintype.card V * (∏ t, (1 - u • Γ t).det) * (1 - u • stepOp Γ).det =
      (1 - u ^ 2) ^ (5 * Fintype.card V) *
        ((1 + 4 * u ^ 2) • (1 : Matrix V V R) - u • ∑ t, Γ t).det := by
  have hG2 : blockDiagonal Γ * blockDiagonal Γ = 1 := by
    rw [← blockDiagonal_mul]
    simp only [hΓ]
    exact blockDiagonal_one
  have hdetG : (1 - u • blockDiagonal Γ).det = ∏ t, (1 - u • Γ t).det := by
    have h : (blockDiagonal fun t => 1 - u • Γ t) = 1 - u • blockDiagonal Γ := by
      rw [show (fun t => 1 - u • Γ t) = (1 : Fin 5 → Matrix V V R) - u • Γ from rfl,
        blockDiagonal_sub, blockDiagonal_one, blockDiagonal_smul]
    rw [← h, det_blockDiagonal]
  have h1 : (1 - u • blockDiagonal Γ) *
      (blockDiagonal Γ * (colX V R * rowY V R) - blockDiagonal Γ) =
      (blockDiagonal Γ * (colX V R * rowY V R) - blockDiagonal Γ) -
        u • (colX V R * rowY V R - 1) := by
    rw [sub_mul, Matrix.one_mul, Matrix.smul_mul, mul_sub,
      ← Matrix.mul_assoc (blockDiagonal Γ) (blockDiagonal Γ), hG2, Matrix.one_mul]
  have hprod : (1 - u • blockDiagonal Γ) * (1 - u • stepOp Γ) =
      (1 - u ^ 2) • (1 : Matrix (V × Fin 5) (V × Fin 5) R) -
        (u • (blockDiagonal Γ - u • 1) * colX V R) * rowY V R := by
    rw [stepOp_eq, mul_sub, Matrix.mul_one, Matrix.mul_smul, h1]
    simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    module
  have hYZ : rowY V R * (u • (blockDiagonal Γ - u • 1) * colX V R) =
      u • ∑ t, Γ t - (5 * u ^ 2) • (1 : Matrix V V R) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, ← Matrix.mul_assoc, rowY_blockDiagonal_colX,
      rowY_mul_colX]
    module
  have hsyl := det_sylvester (1 - u ^ 2) (u • (blockDiagonal Γ - u • 1) * colX V R) (rowY V R)
  rw [← hprod, det_mul, hdetG, hYZ] at hsyl
  have hfin : (1 - u ^ 2) • (1 : Matrix V V R) - (u • ∑ t, Γ t - (5 * u ^ 2) • 1) =
      (1 + 4 * u ^ 2) • (1 : Matrix V V R) - u • ∑ t, Γ t := by
    module
  rw [hfin, Fintype.card_prod, Fintype.card_fin, mul_comm (Fintype.card V) 5] at hsyl
  rw [← hsyl]
  ring

end General

/-! ## Polynomials agreeing off `±1` agree everywhere -/

theorem extend_from_generic {f g : ℂ → ℂ} {p q : Polynomial ℂ} (hf : ∀ u, f u = p.eval u)
    (hg : ∀ u, g u = q.eval u) (h : ∀ u : ℂ, u ^ 2 ≠ 1 → f u = g u) : ∀ u, f u = g u := by
  have hpq : p = q := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hsub : {u : ℂ | u ^ 2 = 1}ᶜ ⊆ {x | p.eval x = q.eval x} := by
      intro u hu
      have hu' : u ^ 2 ≠ 1 := hu
      change p.eval u = q.eval u
      rw [← hf, ← hg]
      exact h u hu'
    refine Set.Infinite.mono hsub ?_
    have hfin : ({u : ℂ | u ^ 2 = 1} : Set ℂ).Finite := by
      have : {u : ℂ | u ^ 2 = 1} ⊆ (({1, -1} : Finset ℂ) : Set ℂ) := by
        intro u hu
        have hu' : u ^ 2 = 1 := hu
        have : (u - 1) * (u + 1) = 0 := by linear_combination hu'
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        rcases mul_eq_zero.mp this with h1 | h1
        · exact Or.inl (by linear_combination h1)
        · exact Or.inr (by linear_combination h1)
      exact (Finset.finite_toSet _).subset this
    exact hfin.infinite_compl
  intro u
  rw [hf, hg, hpq]

/-- The determinant of `1 − u • M` is a polynomial in `u`. -/
theorem det_one_sub_smul_poly {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    ∀ u : ℂ, (1 - u • M).det =
      (1 - (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C).det.eval u := by
  intro u
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp <;> ring
  · simp [Matrix.one_apply, h] <;> ring

/-! ## The sixteen two-spinor states: the transitions and their characters -/

/-- The transition of the change `t` as a matrix on the sixteen two-spinor states, over `ℤ`. -/
def transitionMatZ (t : Fin 5) : Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.of fun k' k => if k' = transition t k then 1 else 0

/-- The character table of the sixteen two-spinor states: `χ_l(k) = (−1)^{|T_k ∩ T_l|}`. -/
def charTable : Matrix (Fin 16) (Fin 16) ℤ :=
  !![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1;
     1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1;
     1, -1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, 1, 1, 1;
     1, -1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1, -1, -1, 1;
     1, -1, -1, -1, 1, -1, 1, 1, -1, 1, 1, -1, 1, -1, 1, -1;
     1, -1, -1, -1, -1, 1, 1, 1, 1, -1, 1, 1, -1, 1, -1, -1;
     1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, 1, 1;
     1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, 1, 1, -1, -1, 1;
     1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1;
     1, -1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1, 1, -1, -1;
     1, 1, -1, -1, 1, 1, -1, -1, 1, 1, 1, -1, -1, -1, -1, 1;
     1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1;
     1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1, -1, -1;
     1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, 1, 1, -1, -1;
     1, 1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1;
     1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, -1, -1, 1]

/-- The table is the characters: `χ_l(k) = (−1)^{|T_k ∩ T_l|}`. -/
theorem charTable_eq :
    charTable = Matrix.of fun k l => (-1) ^ (disagreeSet k ∩ disagreeSet l).card := by
  decide +kernel

/-- The eigenvalue of the change `t` on the character `l`: `−1` when `t ∈ T_l`. -/
def charSign (t : Fin 5) (l : Fin 16) : ℤ := if t ∈ disagreeSet l then -1 else 1

/-- The eigenvalue of the walk on the character `l`: `5 − 2|T_l|`. -/
def charValue (l : Fin 16) : ℤ := 5 - 2 * (disagreeSet l).card

theorem charTable_mul_self : charTable * charTable = (16 : ℤ) • 1 := by
  decide +kernel

theorem transitionMatZ_mul_charTable (t : Fin 5) :
    transitionMatZ t * charTable = charTable * Matrix.diagonal (charSign t) := by
  revert t
  decide +kernel

theorem transitionMatZ_mul_self (t : Fin 5) : transitionMatZ t * transitionMatZ t = 1 := by
  revert t
  decide +kernel

/-- The adjacency of the sixteen two-spinor states (the Clebsch graph). -/
def adjacencyZ : Matrix (Fin 16) (Fin 16) ℤ := ∑ t, transitionMatZ t

theorem adjacency_mul_charTable :
    adjacencyZ * charTable = charTable * Matrix.diagonal charValue := by
  decide +kernel

/-- **In the characters the walk is the comparison less one:** the eigenvalue of the walk on the
character `l` is `L_l − 1`, with `L_l = 6 − 2|T_l|` the comparison on the two-spinor state `e_l`
(Proposition 10): `5, 1, −3` on `1, 10, 5` characters. -/
theorem charValue_eq_L (l : Fin 16) : charValue l = Lvalue l - 1 := by
  simp only [charValue, Lvalue]
  ring

theorem charValue_values :
    (List.finRange 16).map charValue = [5, -3, -3, -3, -3, -3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  decide

theorem charSign_count (t : Fin 5) :
    (Finset.univ.filter fun l => charSign t l = -1).card = 8 := by
  revert t
  decide

/-! ## Determinants through a diagonalization -/

/-- The character table over `ℂ`. -/
noncomputable def charTableC : Matrix (Fin 16) (Fin 16) ℂ := charTable.map (Int.castRingHom ℂ)

/-- The transitions of the sixteen two-spinor states over `ℂ`. -/
noncomputable def transitionMat (t : Fin 5) : Matrix (Fin 16) (Fin 16) ℂ :=
  (transitionMatZ t).map (Int.castRingHom ℂ)

theorem map_diagonal_int (d : Fin 16 → ℤ) :
    (Matrix.diagonal d).map (Int.castRingHom ℂ) = Matrix.diagonal fun l => (d l : ℂ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem map_one_int : (1 : Matrix (Fin 16) (Fin 16) ℤ).map (Int.castRingHom ℂ) = 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem charTableC_mul_self : charTableC * charTableC = (16 : ℂ) • 1 := by
  rw [charTableC, ← Matrix.map_mul, charTable_mul_self]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/-- If `M H = H D` with `D` diagonal and `H` the character table, then
`det(a − uM) = ∏_l (a − u d_l)`. -/
theorem det_of_diag (M : Matrix (Fin 16) (Fin 16) ℂ) (d : Fin 16 → ℂ)
    (hM : M * charTableC = charTableC * diagonal d) (a u : ℂ) :
    (a • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • M).det = ∏ l, (a - u * d l) := by
  have hdetH : charTableC.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det charTableC_mul_self
    rw [det_mul, h, zero_mul, det_smul, det_one, mul_one] at this
    norm_num at this
  have hdiag : (diagonal fun l => a - u * d l) =
      a • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • diagonal d := by
    ext i j
    simp only [diagonal_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  have hkey : (a • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • M) * charTableC =
      charTableC * diagonal fun l => a - u * d l := by
    rw [hdiag, sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, hM, mul_sub,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]
  have := congrArg Matrix.det hkey
  rw [det_mul, det_mul, det_diagonal, mul_comm] at this
  exact mul_left_cancel₀ hdetH this

theorem transitionMat_mul_charTable (t : Fin 5) :
    transitionMat t * charTableC = charTableC * diagonal fun l => ((charSign t l : ℤ) : ℂ) := by
  rw [transitionMat, charTableC, ← Matrix.map_mul, transitionMatZ_mul_charTable, Matrix.map_mul,
    map_diagonal_int]

theorem transitionMat_mul_self (t : Fin 5) : transitionMat t * transitionMat t = 1 := by
  rw [transitionMat, ← Matrix.map_mul, transitionMatZ_mul_self, map_one_int]

theorem prod_charSign (t : Fin 5) (u : ℂ) :
    ∏ l, (1 - u * ((charSign t l : ℤ) : ℂ)) = (1 - u ^ 2) ^ 8 := by
  fin_cases t <;>
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, charSign]
    simp [disagreeSet]
    ring

theorem det_one_sub_transitionMat (t : Fin 5) (u : ℂ) :
    (1 - u • transitionMat t).det = (1 - u ^ 2) ^ 8 := by
  have h := det_of_diag (transitionMat t) (fun l => ((charSign t l : ℤ) : ℂ)) (transitionMat_mul_charTable t)
    1 u
  rw [one_smul] at h
  rw [h, prod_charSign]

theorem adjacency_mul_charTable_C :
    (∑ t, transitionMat t) * charTableC = charTableC * diagonal fun l => ((charValue l : ℤ) : ℂ) := by
  have : (∑ t, transitionMat t) = adjacencyZ.map (Int.castRingHom ℂ) := by
    ext i j
    simp [transitionMat, adjacencyZ, Matrix.sum_apply]
  rw [this, charTableC, ← Matrix.map_mul, adjacency_mul_charTable, Matrix.map_mul,
    map_diagonal_int]

theorem det_vertex_plus (u : ℂ) :
    ((1 + 4 * u ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • ∑ t, transitionMat t).det =
      (1 - u) * (1 - 4 * u) * (1 - u + 4 * u ^ 2) ^ 10 * (1 + 3 * u + 4 * u ^ 2) ^ 5 := by
  rw [det_of_diag _ _ adjacency_mul_charTable_C]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, charValue]
  simp [disagreeSet]
  ring

/-- **`D₊`:** on the sixteen two-spinor states, for every `u`,
`det(1 − uB₊) = (1 − u²)²⁴ (1 − u)(1 − 4u)(1 − u + 4u²)¹⁰(1 + 3u + 4u²)⁵`. -/
theorem D_plus (u : ℂ) :
    (1 - u • stepOp transitionMat).det =
      (1 - u ^ 2) ^ 24 * (1 - u) * (1 - 4 * u) * (1 - u + 4 * u ^ 2) ^ 10 *
        (1 + 3 * u + 4 * u ^ 2) ^ 5 := by
  revert u
  refine extend_from_generic (p := (1 - (Polynomial.X : Polynomial ℂ) •
      (stepOp transitionMat).map Polynomial.C).det)
    (q := (1 - Polynomial.X ^ 2) ^ 24 * (1 - Polynomial.X) * (1 - 4 * Polynomial.X) *
      (1 - Polynomial.X + 4 * Polynomial.X ^ 2) ^ 10 *
      (1 + 3 * Polynomial.X + 4 * Polynomial.X ^ 2) ^ 5)
    (det_one_sub_smul_poly _) (fun u => by simp) ?_
  intro u hu
  have h := ihara_bass transitionMat transitionMat_mul_self u
  simp only [det_one_sub_transitionMat, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    det_vertex_plus] at h
  have hc : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h56 : (1 - u ^ 2) ^ 56 ≠ 0 := pow_ne_zero _ hc
  apply mul_left_cancel₀ h56
  linear_combination h

/-! ## The signed step: `Γ_t = γ_t ⊗ 1` -/

/-- The lines applied to one system of a two-spinor state: `γ_t ⊗ 1` on the sixteen amplitudes. -/
noncomputable def lineOnRel (t : Fin 5) : Matrix Two Two ℂ := γ t ⊗ₖ (1 : Matrix Four Four ℂ)

theorem lineOnRel_mul_self (t : Fin 5) : lineOnRel t * lineOnRel t = 1 := by
  rw [lineOnRel, ← Matrix.mul_kronecker_mul, γ_mul_self, Matrix.mul_one, Matrix.one_kronecker_one]

theorem sum_γZ_sq : (∑ t, γZ t) * (∑ t, γZ t) = (5 : GaussianInt) • (1 : Matrix Four Four _) := by
  decide +kernel

/-- `(Σ_t γ_t)² = 5`. -/
theorem sum_γ_sq : (∑ t, γ t) * (∑ t, γ t) = (5 : ℂ) • (1 : Matrix Four Four ℂ) := by
  have h : (∑ t, γ t) = (∑ t, γZ t).map GaussianInt.toComplex := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← γZ_map]
    rfl
  rw [h, ← Matrix.map_mul, sum_γZ_sq]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp [map_ofNat]

theorem sum_lineOnRel : (∑ t, lineOnRel t) = (∑ t, γ t) ⊗ₖ (1 : Matrix Four Four ℂ) := by
  ext i j
  simp [lineOnRel, Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

/-- **`A₋ = Σ_t γ_t ⊗ 1` squares to five.** -/
theorem Aminus_sq : (∑ t, lineOnRel t) * (∑ t, lineOnRel t) = (5 : ℂ) • 1 := by
  rw [sum_lineOnRel, ← Matrix.mul_kronecker_mul, Matrix.mul_one, sum_γ_sq, Matrix.smul_kronecker,
    Matrix.one_kronecker_one]

theorem sub_kronecker' {n m : Type*} (A B : Matrix n n ℂ) (C : Matrix m m ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext i j
  simp [Matrix.kroneckerMap_apply, sub_mul]

theorem det_one_sub_lineOnRel (t : Fin 5) (u : ℂ) :
    (1 - u • lineOnRel t).det = (1 - u ^ 2) ^ 8 := by
  have h1 : (1 : Matrix Two Two ℂ) - u • lineOnRel t =
      (1 - u • γ t) ⊗ₖ (1 : Matrix Four Four ℂ) := by
    rw [sub_kronecker', Matrix.one_kronecker_one, lineOnRel, Matrix.smul_kronecker]
  have h2 : (1 - u • γ t).det = (1 - u ^ 2) ^ 2 := by
    have := det_cone 1 (fun s => if s = t then -u else 0)
    have hs : (∑ s, (if s = t then -u else 0) • γ s) = -(u • γ t) := by
      simp
    have hs2 : (∑ s : Fin 5, (if s = t then -u else 0) ^ 2) = u ^ 2 := by
      simp [ite_pow]
    rw [hs, hs2, one_smul, ← sub_eq_add_neg, one_pow] at this
    exact this
  rw [h1, det_kronecker, h2, det_one, one_pow, mul_one]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

theorem det_vertex_minus (u : ℂ) :
    ((1 + 4 * u ^ 2) • (1 : Matrix Two Two ℂ) - u • ∑ t, lineOnRel t).det =
      (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 8 := by
  have h1 : (1 + 4 * u ^ 2) • (1 : Matrix Two Two ℂ) - u • ∑ t, lineOnRel t =
      ((1 + 4 * u ^ 2) • (1 : Matrix Four Four ℂ) - u • ∑ t, γ t) ⊗ₖ
        (1 : Matrix Four Four ℂ) := by
    rw [sum_lineOnRel, sub_kronecker', Matrix.smul_kronecker, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  have h2 : ((1 + 4 * u ^ 2) • (1 : Matrix Four Four ℂ) - u • ∑ t, γ t).det =
      (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 := by
    have := det_cone (1 + 4 * u ^ 2) (fun _ => -u)
    have hs : (∑ s : Fin 5, (-u) • γ s) = -(u • ∑ t, γ t) := by
      rw [Finset.smul_sum]
      simp
    rw [hs, ← sub_eq_add_neg] at this
    rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [h1, det_kronecker, h2, det_one, one_pow, mul_one]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- **`D₋`:** with the sign of each step, for every `u`,
`det(1 − uB₋) = (1 − u²)²⁴ (1 + 3u² + 16u⁴)⁸`. -/
theorem D_minus (u : ℂ) :
    (1 - u • stepOp lineOnRel).det = (1 - u ^ 2) ^ 24 * (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 8 := by
  revert u
  refine extend_from_generic (p := (1 - (Polynomial.X : Polynomial ℂ) •
      (stepOp lineOnRel).map Polynomial.C).det)
    (q := (1 - Polynomial.X ^ 2) ^ 24 * (1 + 3 * Polynomial.X ^ 2 + 16 * Polynomial.X ^ 4) ^ 8)
    (det_one_sub_smul_poly _) (fun u => by simp) ?_
  intro u hu
  have h := ihara_bass lineOnRel lineOnRel_mul_self u
  simp only [det_one_sub_lineOnRel, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    det_vertex_minus, Fintype.card_prod] at h
  have hc : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h56 : (1 - u ^ 2) ^ 56 ≠ 0 := pow_ne_zero _ hc
  apply mul_left_cancel₀ h56
  linear_combination h

/-- **The opposite phase:** `D₊(u) D₊(−u) = (1 − u²)⁴⁹(1 − 16u²)(1 + 7u² + 16u⁴)¹⁰(1 − u² + 16u⁴)⁵`. -/
theorem D_plus_opposite (u : ℂ) :
    (1 - u • stepOp transitionMat).det * (1 - (-u) • stepOp transitionMat).det =
      (1 - u ^ 2) ^ 49 * (1 - 16 * u ^ 2) * (1 + 7 * u ^ 2 + 16 * u ^ 4) ^ 10 *
        (1 - u ^ 2 + 16 * u ^ 4) ^ 5 := by
  rw [D_plus, D_plus]
  ring

/-- **At `u = 1/4` the factor `1 − 4u` of `D₊` vanishes and every other factor is nonzero.** -/
theorem D_plus_quarter :
    (1 - (1 / 4 : ℂ) • stepOp transitionMat).det = 0 ∧
    (1 - (1 / 4 : ℂ) ^ 2) ^ 24 * (1 - 1 / 4) * (1 - 1 / 4 + 4 * (1 / 4) ^ 2) ^ 10 *
      (1 + 3 * (1 / 4) + 4 * (1 / 4 : ℂ) ^ 2) ^ 5 ≠ 0 := by
  constructor
  · rw [D_plus]
    ring
  · norm_num

/-- **`D₋` does not vanish at `u = 1/4`:** `D₋(1/4) = (15/16)²⁴ (5/4)⁸`. -/
theorem D_minus_quarter :
    (1 - (1 / 4 : ℂ) • stepOp lineOnRel).det = (15 / 16) ^ 24 * (5 / 4) ^ 8 := by
  rw [D_minus]
  norm_num

end Comparison

end
