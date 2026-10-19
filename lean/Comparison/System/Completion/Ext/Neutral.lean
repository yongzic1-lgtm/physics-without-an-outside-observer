import Mathlib
import Comparison.Elements.TwoThings

set_option linter.style.longLine false

/-!
# The proof system, the completions: the heavy neutral exponent (rows T01, T02)

Order the five directions as `h = 0`, `k = 1` and the three colour lines `2, 3, 4`, so that
`ℂ⁵ = ℂh ⊕ ℂk ⊕ C`. The algebra kept by the colour–plane split, the volume and the direction `h` of the last step is

  `k = {X(A) = diag(0, −Tr A, A) : A ∈ u(3)} ⊂ su(5)`,

the generator `A` on `C`, `0` on `h` and `−Tr A` on `k`.

* `finrank_u3`, `finrank_kept`: **`k` has real dimension `9 = 3 + 2·C(3, 2)`**, three imaginary diagonal entries and
  three complex off-diagonal ones; `kept_su5`: every `X ∈ k` is anti-Hermitian and traceless and fixes `h`.
* `hop a b`: the exterior representation `c_a†c_b` on the sixteen even states (the even subsets of the five lines,
  in the order of `disagreeSet`, `evenMask_disagreeSet`), with the alternating signs; `hop_number`: `c_b†c_b` counts
  the line `b`; `hop_singlet`: **every `c_a†c_b` annihilates the singlet and never reaches it**.
* `keptN`: the nine generators of `k` on the sixteen states, `ρ(X) = Σ X_ab c_a†c_b`, in their real forms
  (`ρ(X_i) = i^{ε_i} keptN i`): `n_c − n_k`, `c_c†c_d − c_d†c_c`, `c_c†c_d + c_d†c_c`; `keptN_eq`: they are `ρ` of the
  integer forms of the generators; `keptN_gram`: **their Gram `Tr(N_iᵀN_j)` is
  `G = [[8, 4, 4], [4, 8, 4], [4, 4, 8]] ⊕ 8I₆`**.
* `Dcoh`: the coherent comparison `|L|/L(Ω)` on the sixteen states, `Dcoh_eq`: `Π₀ + (I − Π₀)/3`; `Dcoh_mul`: on every
  map that never reaches the singlet it is `1/3`; `keptH_eq`: **the pulled-back Gram is `H = G/3`**.
* `retained_det`: **`det(G⁻¹H) = (1/3)^{dim k} = 3⁻⁹`**, by `Matrix.det_smul`.
* `acrossN`: the six complex directions of `Hom_ℂ(F, C)`, `F = {h, k}`, `ρ(E_cf) = c_c†c_f`; `acrossN_gram`: Gram
  `4I₆`; `acrossH_eq`: `H_off = G_off/3`; `across_det`: **`det_ℂ(G_off⁻¹H_off) = (1/3)^{dim_ℂ Hom(F, C)} = 3⁻⁶`**.

The rows `T01 = M_Pl det(G⁻¹H) = M_Pl 3⁻⁹` and `T02 = M_Pl det_ℂ(G_off⁻¹H_off) = M_Pl 3⁻⁶ = 27 T01` read these
(`Completion/Numbers.lean`, `Num.neutralR`, `Num.neutralOff`).
-/

namespace Comparison.System.Completion.Neutral

open Matrix Complex Module

/-! ## The kept algebra and its real dimension -/

/-- `u(3)`: the anti-Hermitian `3 × 3` complex matrices. -/
def u3 : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℂ) where
  carrier := {X | Xᴴ = -X}
  add_mem' := by
    intro X Y hX hY
    have hX' : Xᴴ = -X := hX
    have hY' : Yᴴ = -Y := hY
    show (X + Y)ᴴ = -(X + Y)
    rw [conjTranspose_add, hX', hY', neg_add]
  zero_mem' := by
    show (0 : Matrix (Fin 3) (Fin 3) ℂ)ᴴ = -0
    simp
  smul_mem' := by
    intro c X hX
    have hX' : Xᴴ = -X := hX
    show (c • X)ᴴ = -(c • X)
    rw [conjTranspose_smul, hX', smul_neg]
    simp

/-- The nine real coordinates of `u(3)`: the imaginary diagonal entries `c₀, c₁, c₂` and the off-diagonal entries
`c₃ + ic₄`, `c₅ + ic₆`, `c₇ + ic₈`. -/
noncomputable def u3Of (c : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(c 0 : ℂ) * I, (c 3 : ℂ) + (c 4 : ℂ) * I, (c 5 : ℂ) + (c 6 : ℂ) * I;
     -(c 3 : ℂ) + (c 4 : ℂ) * I, (c 1 : ℂ) * I, (c 7 : ℂ) + (c 8 : ℂ) * I;
     -(c 5 : ℂ) + (c 6 : ℂ) * I, -(c 7 : ℂ) + (c 8 : ℂ) * I, (c 2 : ℂ) * I]

/-- The coordinates, as a real-linear map. -/
noncomputable def u3Lin : (Fin 9 → ℝ) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun := u3Of
  map_add' c d := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u3Of] <;> ring
  map_smul' a c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u3Of, Complex.real_smul] <;> ring

theorem u3Lin_apply (c : Fin 9 → ℝ) : u3Lin c = u3Of c := rfl

theorem u3Lin_injective : Function.Injective u3Lin := by
  intro c d h
  rw [u3Lin_apply, u3Lin_apply] at h
  have e : ∀ i j : Fin 3, u3Of c i j = u3Of d i j := fun i j => by rw [h]
  have h00 := congrArg Complex.im (e 0 0)
  have h11 := congrArg Complex.im (e 1 1)
  have h22 := congrArg Complex.im (e 2 2)
  have h01r := congrArg Complex.re (e 0 1)
  have h01i := congrArg Complex.im (e 0 1)
  have h02r := congrArg Complex.re (e 0 2)
  have h02i := congrArg Complex.im (e 0 2)
  have h12r := congrArg Complex.re (e 1 2)
  have h12i := congrArg Complex.im (e 1 2)
  simp [u3Of] at h00 h11 h22 h01r h01i h02r h02i h12r h12i
  funext k
  fin_cases k
  · exact h00
  · exact h11
  · exact h22
  · exact h01r
  · exact h01i
  · exact h02r
  · exact h02i
  · exact h12r
  · exact h12i

theorem u3Of_mem (c : Fin 9 → ℝ) : u3Of c ∈ u3 := by
  show (u3Of c)ᴴ = -u3Of c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u3Of, conjTranspose_apply] <;> ring

theorem mem_u3_eq (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : X ∈ u3) :
    u3Of ![(X 0 0).im, (X 1 1).im, (X 2 2).im, (X 0 1).re, (X 0 1).im, (X 0 2).re, (X 0 2).im,
      (X 1 2).re, (X 1 2).im] = X := by
  have h1 : Xᴴ = -X := hX
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
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [u3Of]
  all_goals first
    | linarith [hd 0, hd 1, hd 2, hre 0 1, hre 0 2, hre 1 2, him 0 1, him 0 2, him 1 2]
    | (rw [hd 0]) | (rw [hd 1]) | (rw [hd 2])

theorem range_u3Lin : LinearMap.range u3Lin = u3 := by
  ext X
  constructor
  · rintro ⟨c, rfl⟩
    exact u3Of_mem c
  · intro hX
    exact ⟨_, mem_u3_eq X hX⟩

/-- **`u(3)` has real dimension nine.** -/
theorem finrank_u3 : finrank ℝ u3 = 9 := by
  rw [← range_u3Lin, LinearMap.finrank_range_of_inj u3Lin_injective, Module.finrank_fin_fun]

/-- `X(A) = diag(0, −Tr A, A)` on `ℂ⁵`: `0` on `h`, `−Tr A` on `k`, `A` on the colour lines. -/
noncomputable def keptOf (A : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 0, 0, 0, 0;
     0, -A.trace, 0, 0, 0;
     0, 0, A 0 0, A 0 1, A 0 2;
     0, 0, A 1 0, A 1 1, A 1 2;
     0, 0, A 2 0, A 2 1, A 2 2]

/-- `A ↦ X(A)`, real-linear. -/
noncomputable def keptLin : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℝ] Matrix (Fin 5) (Fin 5) ℂ where
  toFun := keptOf
  map_add' A B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [keptOf, Matrix.trace_add] <;> ring
  map_smul' a A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [keptOf, Matrix.trace_smul, Complex.real_smul] <;> ring

theorem keptLin_injective : Function.Injective keptLin := by
  intro A B h
  have e : ∀ i j : Fin 5, keptOf A i j = keptOf B i j := fun i j => by
    have := congrFun (congrFun h i) j
    exact this
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | simpa [keptOf] using e 2 2 | simpa [keptOf] using e 2 3 | simpa [keptOf] using e 2 4
    | simpa [keptOf] using e 3 2 | simpa [keptOf] using e 3 3 | simpa [keptOf] using e 3 4
    | simpa [keptOf] using e 4 2 | simpa [keptOf] using e 4 3 | simpa [keptOf] using e 4 4

/-- **The kept algebra** `k = {X(A) : A ∈ u(3)}`. -/
noncomputable def kept : Submodule ℝ (Matrix (Fin 5) (Fin 5) ℂ) := u3.map keptLin

/-- **The kept algebra has real dimension nine**, `3 + 2·C(3, 2)`. -/
theorem finrank_kept : finrank ℝ kept = 9 := by
  rw [kept, ← (Submodule.equivMapOfInjective keptLin keptLin_injective u3).finrank_eq, finrank_u3]

theorem nine_coordinates : 3 + 2 * Nat.choose 3 2 = 9 := by decide

/-- **`k ⊂ su(5)`, and `k` fixes `h`:** every `X ∈ k` is anti-Hermitian and traceless, with row and column `h` zero. -/
theorem kept_su5 (X : Matrix (Fin 5) (Fin 5) ℂ) (hX : X ∈ kept) :
    Xᴴ = -X ∧ X.trace = 0 ∧ ∀ b : Fin 5, X 0 b = 0 ∧ X b 0 = 0 := by
  obtain ⟨A, hA, rfl⟩ := hX
  have h1 : Aᴴ = -A := hA
  have hs : ∀ i j, star (A j i) = -A i j := fun i j => by
    have := congrFun (congrFun h1 i) j
    simpa [conjTranspose_apply] using this
  have htr : star A.trace = -A.trace := by
    rw [← Matrix.trace_conjTranspose, h1, Matrix.trace_neg]
  refine ⟨?_, ?_, fun b => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [keptLin, keptOf, conjTranspose_apply, hs, htr]
  · simp [keptLin, keptOf, Matrix.trace, Fin.sum_univ_five, Fin.sum_univ_three] <;> ring
  · fin_cases b <;> simp [keptLin, keptOf]

/-! ## The exterior representation on the sixteen even states -/

/-- The sixteen even states as bit masks over the five lines, in the order of `disagreeSet`. -/
def evenMask : Fin 16 → ℕ := ![0, 30, 29, 27, 23, 15, 3, 5, 9, 17, 6, 10, 18, 12, 20, 24]

theorem evenMask_disagreeSet :
    ∀ k : Fin 16, (Finset.univ.filter fun i : Fin 5 => (evenMask k).testBit i.val) = disagreeSet k := by
  decide +kernel

/-- The occupied lines of the mask `m` below the line `b`. -/
def bitsBelow (m b : ℕ) : ℕ := ((List.range b).filter fun i => m.testBit i).length

/-- **`c_a†c_b` on the sixteen even states**, with the alternating signs
`(−1)^{|{x ∈ S, x < b}|}(−1)^{|{x ∈ S ∖ b, x < a}|}`. -/
def hop (a b : Fin 5) : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of fun T S =>
  if (evenMask S).testBit b.val ∧ ¬ (evenMask S - 2 ^ b.val).testBit a.val ∧
      evenMask T = evenMask S - 2 ^ b.val + 2 ^ a.val then
    (-1) ^ (bitsBelow (evenMask S) b.val + bitsBelow (evenMask S - 2 ^ b.val) a.val)
  else 0

/-- `c_b†c_b` counts the line `b`. -/
theorem hop_number : ∀ b : Fin 5, hop b b = Matrix.diagonal fun S => if (evenMask S).testBit b.val then 1 else 0 := by
  decide +kernel

/-- **Every `c_a†c_b` annihilates the singlet and never reaches it.** -/
theorem hop_singlet : ∀ a b : Fin 5, ∀ S : Fin 16, hop a b S 0 = 0 ∧ hop a b 0 S = 0 := by
  decide +kernel

/-- The integer forms of the nine generators of `k` on `ℂ⁵`: `E_cc − E_kk` (`c = 2, 3, 4`), then `E_cd − E_dc` and
`E_cd + E_dc` for `cd = 23, 24, 34`; the generators are `X_i = i^{ε_i}` times these, `ε = (1, 1, 1, 0, 1, 0, 1, 0, 1)`. -/
def keptZ : Fin 9 → Matrix (Fin 5) (Fin 5) ℤ := fun i => Matrix.of fun a b =>
  match i.val with
  | 0 => if a = b ∧ a = 2 then 1 else if a = b ∧ a = 1 then -1 else 0
  | 1 => if a = b ∧ a = 3 then 1 else if a = b ∧ a = 1 then -1 else 0
  | 2 => if a = b ∧ a = 4 then 1 else if a = b ∧ a = 1 then -1 else 0
  | 3 => if a = 2 ∧ b = 3 then 1 else if a = 3 ∧ b = 2 then -1 else 0
  | 4 => if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 1 else 0
  | 5 => if a = 2 ∧ b = 4 then 1 else if a = 4 ∧ b = 2 then -1 else 0
  | 6 => if (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) then 1 else 0
  | 7 => if a = 3 ∧ b = 4 then 1 else if a = 4 ∧ b = 3 then -1 else 0
  | _ => if (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) then 1 else 0

/-- `ρ(X) = Σ X_ab c_a†c_b` for an integer matrix `X`. -/
def rhoZ (X : Matrix (Fin 5) (Fin 5) ℤ) : Matrix (Fin 16) (Fin 16) ℤ := ∑ a, ∑ b, X a b • hop a b

/-- The nine generators of `k` on the sixteen states, in their real forms. -/
def keptN : Fin 9 → Matrix (Fin 16) (Fin 16) ℤ :=
  ![hop 2 2 - hop 1 1, hop 3 3 - hop 1 1, hop 4 4 - hop 1 1,
    hop 2 3 - hop 3 2, hop 2 3 + hop 3 2, hop 2 4 - hop 4 2, hop 2 4 + hop 4 2,
    hop 3 4 - hop 4 3, hop 3 4 + hop 4 3]

/-- `keptN i = ρ(keptZ i)`. -/
theorem keptN_eq : keptN = fun i => rhoZ (keptZ i) := by
  decide +kernel

/-- The Hilbert–Schmidt Gram `Tr(MᵀN)` of two real maps of the sixteen states. -/
def gramZ (M N : Matrix (Fin 16) (Fin 16) ℤ) : ℤ := (Mᵀ * N).trace

/-- `G = [[8, 4, 4], [4, 8, 4], [4, 4, 8]] ⊕ 8I₆` in the three diagonal and six off-diagonal coordinates. -/
def keptGZ : Matrix (Fin 9) (Fin 9) ℤ :=
  !![8, 4, 4, 0, 0, 0, 0, 0, 0;
     4, 8, 4, 0, 0, 0, 0, 0, 0;
     4, 4, 8, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 8, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 8, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 8, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 8, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 8, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 8]

/-- **The Gram of the nine generators on the sixteen states** is `G`. -/
theorem keptN_gram : (Matrix.of fun i j => gramZ (keptN i) (keptN j)) = keptGZ := by
  decide +kernel

/-- The six complex directions of `Hom_ℂ(F, C)`, `E_cf` with `c ∈ {2, 3, 4}` and `f ∈ {h, k} = {0, 1}`:
`ρ(E_cf) = c_c†c_f`. -/
def acrossN : Fin 6 → Matrix (Fin 16) (Fin 16) ℤ := ![hop 2 0, hop 2 1, hop 3 0, hop 3 1, hop 4 0, hop 4 1]

/-- **Their Gram is `4I₆`.** -/
theorem acrossN_gram : (Matrix.of fun i j => gramZ (acrossN i) (acrossN j)) = (4 : ℤ) • 1 := by
  decide +kernel

theorem keptN_singlet (i : Fin 9) (S : Fin 16) : keptN i 0 S = 0 := by
  revert i S
  decide +kernel

theorem acrossN_singlet (i : Fin 6) (S : Fin 16) : acrossN i 0 S = 0 := by
  revert i S
  decide +kernel

/-! ## The coherent comparison pulled back -/

/-- **The coherent comparison** `D_coh = |L|/L(Ω)` on the sixteen even states, with `L = 6 − 2|S|` (`L_rel'`). -/
def Dcoh : Matrix (Fin 16) (Fin 16) ℚ := Matrix.diagonal fun k => (|Lvalue k| : ℚ) / (Lvalue 0 : ℚ)

theorem Lvalue_cases : ∀ k : Fin 16, Lvalue k = if k = 0 then 6 else if k.val ≤ 5 then -2 else 2 := by
  decide +kernel

/-- `D_coh = Π₀ + (I − Π₀)/3`. -/
theorem Dcoh_eq : Dcoh = Matrix.diagonal fun k => if k = 0 then 1 else 1 / 3 := by
  have h0 : Lvalue 0 = 6 := by decide +kernel
  rw [Dcoh]
  congr 1
  funext k
  rw [Lvalue_cases k, h0]
  split_ifs <;> norm_num

/-- **On every map that never reaches the singlet the coherent comparison is `1/3`.** -/
theorem Dcoh_mul (N : Matrix (Fin 16) (Fin 16) ℤ) (hN : ∀ S, N 0 S = 0) :
    Dcoh * N.map (Int.castRingHom ℚ) = (1 / 3 : ℚ) • N.map (Int.castRingHom ℚ) := by
  rw [Dcoh_eq]
  ext T S
  rw [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  by_cases hT : T = 0
  · subst hT
    simp [hN S]
  · simp [hT]

theorem trace_map_gram (M N : Matrix (Fin 16) (Fin 16) ℤ) :
    ((M.map (Int.castRingHom ℚ))ᵀ * N.map (Int.castRingHom ℚ)).trace = (gramZ M N : ℚ) := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, gramZ]
  simp [Matrix.trace, Matrix.diag]

/-- `G` over `ℚ`. -/
def keptG : Matrix (Fin 9) (Fin 9) ℚ := keptGZ.map (Int.castRingHom ℚ)

/-- **The comparison Gram** `H_ij = Tr(ρ(X_i)ᵀ D_coh ρ(X_j))` of the nine generators. -/
def keptH : Matrix (Fin 9) (Fin 9) ℚ := Matrix.of fun i j =>
  (((keptN i).map (Int.castRingHom ℚ))ᵀ * Dcoh * (keptN j).map (Int.castRingHom ℚ)).trace

/-- **`H = G/3`.** -/
theorem keptH_eq : keptH = (1 / 3 : ℚ) • keptG := by
  ext i j
  rw [keptH, Matrix.of_apply, Matrix.mul_assoc, Dcoh_mul _ (keptN_singlet j), Matrix.mul_smul, Matrix.trace_smul,
    trace_map_gram, Matrix.smul_apply, keptG, Matrix.map_apply, ← keptN_gram]
  simp

/-- `16 G⁻¹`. -/
def keptGinvZ : Matrix (Fin 9) (Fin 9) ℤ :=
  !![3, -1, -1, 0, 0, 0, 0, 0, 0;
     -1, 3, -1, 0, 0, 0, 0, 0, 0;
     -1, -1, 3, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 2, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 2, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 2, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 2, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 2, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 2]

theorem keptGZ_mul_inv : keptGZ * keptGinvZ = (16 : ℤ) • 1 := by
  decide +kernel

theorem keptG_det_isUnit : IsUnit keptG.det := by
  have h : keptG * ((1 / 16 : ℚ) • keptGinvZ.map (Int.castRingHom ℚ)) = 1 := by
    rw [keptG, Matrix.mul_smul, ← Matrix.map_mul, keptGZ_mul_inv]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul, Int.coe_castRingHom]
    split_ifs <;> norm_num
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one (by rw [← Matrix.det_mul, h, Matrix.det_one]))

/-- **The heavy neutral exponent:** `det(G⁻¹H) = (1/3)^{dim k} = 3⁻⁹`, by `Matrix.det_smul`. -/
theorem retained_det : (keptG⁻¹ * keptH).det = (1 / 3 : ℚ) ^ finrank ℝ kept ∧
    (keptG⁻¹ * keptH).det = 1 / 19683 := by
  have h : (keptG⁻¹ * keptH).det = (1 / 3 : ℚ) ^ 9 := by
    rw [keptH_eq, Matrix.mul_smul, Matrix.nonsing_inv_mul _ keptG_det_isUnit, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, mul_one]
  exact ⟨by rw [h, finrank_kept], by rw [h]; norm_num⟩

/-- `det H = 3⁻⁹ det G` (`Matrix.det_smul`). -/
theorem keptH_det : keptH.det = (1 / 3 : ℚ) ^ 9 * keptG.det := by
  rw [keptH_eq, Matrix.det_smul, Fintype.card_fin]

/-! ## The rotations across the split, `Hom_ℂ(F, C)` -/

/-- `G_off = 4I₆`. -/
def acrossG : Matrix (Fin 6) (Fin 6) ℚ := (4 : ℚ) • 1

/-- `H_off`, the coherent comparison pulled back to the six. -/
def acrossH : Matrix (Fin 6) (Fin 6) ℚ := Matrix.of fun i j =>
  (((acrossN i).map (Int.castRingHom ℚ))ᵀ * Dcoh * (acrossN j).map (Int.castRingHom ℚ)).trace

theorem acrossG_eq : (Matrix.of fun i j => (((acrossN i).map (Int.castRingHom ℚ))ᵀ *
    (acrossN j).map (Int.castRingHom ℚ)).trace) = acrossG := by
  ext i j
  rw [Matrix.of_apply, trace_map_gram]
  have := congrFun (congrFun acrossN_gram i) j
  rw [Matrix.of_apply] at this
  rw [this, acrossG]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- **`H_off = G_off/3`.** -/
theorem acrossH_eq : acrossH = (1 / 3 : ℚ) • acrossG := by
  ext i j
  rw [acrossH, Matrix.of_apply, Matrix.mul_assoc, Dcoh_mul _ (acrossN_singlet j), Matrix.mul_smul,
    Matrix.trace_smul, ← acrossG_eq, Matrix.smul_apply, Matrix.of_apply]

theorem finrank_hom : finrank ℂ (Matrix (Fin 3) (Fin 2) ℂ) = 6 := by
  simp [Module.finrank_matrix]

/-- **`det_ℂ(G_off⁻¹H_off) = (1/3)^{dim_ℂ Hom(F, C)} = 3⁻⁶`.** -/
theorem across_det : (acrossG⁻¹ * acrossH).det = (1 / 3 : ℚ) ^ finrank ℂ (Matrix (Fin 3) (Fin 2) ℂ) ∧
    (acrossG⁻¹ * acrossH).det = 1 / 729 := by
  have hu : IsUnit acrossG.det := by
    rw [acrossG, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have h : (acrossG⁻¹ * acrossH).det = (1 / 3 : ℚ) ^ 6 := by
    rw [acrossH_eq, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hu, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, mul_one]
  exact ⟨by rw [h, finrank_hom], by rw [h]; norm_num⟩

end Comparison.System.Completion.Neutral
