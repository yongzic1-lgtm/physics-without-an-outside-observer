import Comparison.System.Postulates
import Comparison.Existence.Closing
import Comparison.Mass.Basic
import Comparison.Mass.Shift

/-!
# The proof system, the law: Proposition 57, closing a level

`K = [[A, B], [C, D]]`, `S = A − BD⁻¹C`,
`L = (1, −BD⁻¹)`, `R = (1; −D⁻¹C)`, `Q = [[0, 0], [0, D⁻¹]]` (`Existence/Closing.lean`, with `⅟D`; here with
the inverse `D⁻¹` of a matrix of nonzero determinant, so that `S` is a function of the sources).

* `schurN`, `schurLN`, `schurRN`, `schurQN`; `schurN_diff`, `schurLN_diff`, `schurRN_diff`: the exact
  differences of `Closing.lean` with `D⁻¹`;
* `schur_source_deriv`: **with a source, `∂_J S = L K_a R`** at `J = 0`, entry by entry;
* `schurLN_deriv`, `schurRN_deriv`: `∂L = −L K_a Q`, `∂R = −Q K_a R`;
* `schur_source_mixed`: **with two sources, `∂_s∂_t S = L(K_ab − K_aQK_b − K_bQK_a)R`** at `s = t = 0`,
  for `K(s, t) = K + sK_a + tK_b + stK_ab`;
* `residue_at_simple_zero`: **at a simple zero `ζ₀` of `det S` with kernels spanned by `r` and `ℓ`,
  `ℓ S_ζ r ≠ 0` and `(ζ − ζ₀) S(ζ)⁻¹ → r ℓᵀ/(ℓ S_ζ r)`**;
* `zero_shift_pencil` (over every `RCLike` field, `ℝ` and `ℂ`): **for `S(ζ, J) = S₀ + (ζ − ζ₀)S_ζ + J S_a` with such kernels and `ℓ S_ζ r ≠ 0`, the zero
  `ζ(J)` of `det S(·, J)` through `ζ₀` exists near `J = 0` and `dζ/dJ = −ℓ S_a r/(ℓ S_ζ r)`**;
* `prop_57`: Proposition 57 as one statement.
-/

open Matrix Filter Topology Comparison

namespace Comparison.System

namespace Law

section Schur

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The reduced operator with the inverse of `D`: `S = A − BD⁻¹C`. -/
noncomputable def schurN (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n m 𝕜) (D : Matrix n n 𝕜) :
    Matrix m m 𝕜 := A - B * D⁻¹ * C

/-- `L = (1, −BD⁻¹)`. -/
noncomputable def schurLN (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) : Matrix m (m ⊕ n) 𝕜 :=
  fromCols 1 (-(B * D⁻¹))

/-- `R = (1; −D⁻¹C)`. -/
noncomputable def schurRN (C : Matrix n m 𝕜) (D : Matrix n n 𝕜) : Matrix (m ⊕ n) m 𝕜 :=
  fromRows 1 (-(D⁻¹ * C))

/-- `Q = [[0, 0], [0, D⁻¹]]`. -/
noncomputable def schurQN (D : Matrix n n 𝕜) : Matrix (m ⊕ n) (m ⊕ n) 𝕜 := fromBlocks 0 0 0 D⁻¹

theorem schurN_eq (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n m 𝕜) (D : Matrix n n 𝕜)
    [Invertible D] : schurN A B C D = schurS A B C D := by
  rw [schurN, schurS, Matrix.invOf_eq_nonsing_inv]

theorem schurLN_eq (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) [Invertible D] :
    schurLN B D = schurL B D := by
  rw [schurLN, schurL, Matrix.invOf_eq_nonsing_inv]

theorem schurRN_eq (C : Matrix n m 𝕜) (D : Matrix n n 𝕜) [Invertible D] :
    schurRN C D = schurR C D := by
  rw [schurRN, schurR, Matrix.invOf_eq_nonsing_inv]

theorem schurQN_eq (D : Matrix n n 𝕜) [Invertible D] : schurQN (m := m) D = schurQ D := by
  rw [schurQN, schurQ, Matrix.invOf_eq_nonsing_inv]

variable {A A' : Matrix m m 𝕜} {B B' : Matrix m n 𝕜} {C C' : Matrix n m 𝕜} {D D' : Matrix n n 𝕜}

/-- **The exact difference of the reduced operators:** `S' − S = L (K' − K) R'`. -/
theorem schurN_diff (hD : D.det ≠ 0) (hD' : D'.det ≠ 0) :
    schurN A' B' C' D' - schurN A B C D =
      schurLN B D * (fromBlocks A' B' C' D' - fromBlocks A B C D) * schurRN C' D' := by
  letI := invertibleOfIsUnitDet D (isUnit_iff_ne_zero.mpr hD)
  letI := invertibleOfIsUnitDet D' (isUnit_iff_ne_zero.mpr hD')
  rw [schurN_eq, schurN_eq, schurLN_eq, schurRN_eq]
  exact schur_diff A' B' C' D'

/-- `L' − L = −L (K' − K) Q'`. -/
theorem schurLN_diff (hD : D.det ≠ 0) (hD' : D'.det ≠ 0) :
    schurLN B' D' - schurLN B D =
      -(schurLN B D * (fromBlocks A' B' C' D' - fromBlocks A B C D) * schurQN (m := m) D') := by
  letI := invertibleOfIsUnitDet D (isUnit_iff_ne_zero.mpr hD)
  letI := invertibleOfIsUnitDet D' (isUnit_iff_ne_zero.mpr hD')
  rw [schurLN_eq, schurLN_eq, schurQN_eq]
  exact schurL_diff A' B' C' D'

/-- `R' − R = −Q (K' − K) R'`. -/
theorem schurRN_diff (hD : D.det ≠ 0) (hD' : D'.det ≠ 0) :
    schurRN C' D' - schurRN C D =
      -(schurQN (m := m) D * (fromBlocks A' B' C' D' - fromBlocks A B C D) * schurRN C' D') := by
  letI := invertibleOfIsUnitDet D (isUnit_iff_ne_zero.mpr hD)
  letI := invertibleOfIsUnitDet D' (isUnit_iff_ne_zero.mpr hD')
  rw [schurRN_eq, schurRN_eq, schurQN_eq]
  exact schurR_diff A' B' C' D'

/-- The difference of two block matrices with an affine source. -/
theorem fromBlocks_source (A Aa : Matrix m m 𝕜) (B Ba : Matrix m n 𝕜) (C Ca : Matrix n m 𝕜)
    (D Da : Matrix n n 𝕜) (s : 𝕜) :
    fromBlocks (A + s • Aa) (B + s • Ba) (C + s • Ca) (D + s • Da) - fromBlocks A B C D =
      s • fromBlocks Aa Ba Ca Da := by
  ext (i | i) (j | j) <;> simp

/-- Near a matrix of nonzero determinant the inverse is continuous along an affine source. -/
theorem continuousAt_inv_source (D Da : Matrix n n 𝕜) (hD : D.det ≠ 0) :
    ContinuousAt (fun s : 𝕜 => (D + s • Da)⁻¹) 0 := by
  have h0 : D + (0 : 𝕜) • Da = D := by simp
  have hinv : ContinuousAt Inv.inv (D + (0 : 𝕜) • Da) := by
    rw [h0]
    refine continuousAt_matrix_inv D ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hD
  have hf : ContinuousAt (fun s : 𝕜 => D + s • Da) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  exact ContinuousAt.comp (f := fun s : 𝕜 => D + s • Da) hinv hf

/-- Along an affine source the determinant stays nonzero near `0`. -/
theorem eventually_det_ne (D Da : Matrix n n 𝕜) (hD : D.det ≠ 0) :
    ∀ᶠ s in 𝓝 (0 : 𝕜), (D + s • Da).det ≠ 0 := by
  have hc : Continuous (fun s : 𝕜 => (D + s • Da).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have h0 : (fun s : 𝕜 => (D + s • Da).det) 0 ≠ 0 := by simpa using hD
  exact hc.continuousAt.eventually_ne h0

/-- The entries of `(D + sD_a)⁻¹` are continuous at `0`. -/
theorem continuousAt_inv_entry (D Da : Matrix n n 𝕜) (hD : D.det ≠ 0) (b c : n) :
    ContinuousAt (fun s : 𝕜 => (D + s • Da)⁻¹ b c) 0 :=
  (continuous_apply_apply b c).continuousAt.comp (continuousAt_inv_source D Da hD)

theorem continuousAt_affine_entry {p q : Type*} (M Ma : Matrix p q 𝕜) (b : p) (c : q) :
    ContinuousAt (fun s : 𝕜 => (M + s • Ma) b c) 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact continuousAt_const.add (continuousAt_id.mul continuousAt_const)

/-- The entries of `R(s) = (1; −D(s)⁻¹C(s))` are continuous at `0`. -/
theorem continuousAt_schurRN_entry (C Ca : Matrix n m 𝕜) (D Da : Matrix n n 𝕜) (hD : D.det ≠ 0)
    (k : m ⊕ n) (j : m) :
    ContinuousAt (fun s : 𝕜 => schurRN (C + s • Ca) (D + s • Da) k j) 0 := by
  rcases k with a | b
  · simp only [schurRN, fromRows_apply_inl]
    exact continuousAt_const
  · simp only [schurRN, fromRows_apply_inr, Matrix.neg_apply, Matrix.mul_apply]
    refine ContinuousAt.neg ?_
    exact tendsto_finsetSum _ fun c _ =>
      (continuousAt_inv_entry D Da hD b c).mul (continuousAt_affine_entry C Ca c j)

/-- The entries of `L(s) = (1, −B(s)D(s)⁻¹)` are continuous at `0`. -/
theorem continuousAt_schurLN_entry (B Ba : Matrix m n 𝕜) (D Da : Matrix n n 𝕜) (hD : D.det ≠ 0)
    (i : m) (k : m ⊕ n) :
    ContinuousAt (fun s : 𝕜 => schurLN (B + s • Ba) (D + s • Da) i k) 0 := by
  rcases k with a | b
  · simp only [schurLN, fromCols_apply_inl]
    exact continuousAt_const
  · simp only [schurLN, fromCols_apply_inr, Matrix.neg_apply, Matrix.mul_apply]
    refine ContinuousAt.neg ?_
    exact tendsto_finsetSum _ fun c _ =>
      (continuousAt_affine_entry B Ba i c).mul (continuousAt_inv_entry D Da hD c b)

/-- The entries of `Q(s) = [[0, 0], [0, D(s)⁻¹]]` are continuous at `0`. -/
theorem continuousAt_schurQN_entry (D Da : Matrix n n 𝕜) (hD : D.det ≠ 0) (k l : m ⊕ n) :
    ContinuousAt (fun s : 𝕜 => schurQN (m := m) (D + s • Da) k l) 0 := by
  rcases k with a | b <;> rcases l with c | d <;>
    simp only [schurQN, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply]
  · exact continuousAt_const
  · exact continuousAt_const
  · exact continuousAt_const
  · exact continuousAt_inv_entry D Da hD b d

/-- An entry of `X Y Z(s)` is continuous when the entries of `Z` are. -/
theorem continuousAt_entry_mul {p q r : Type*} [Fintype p] [Fintype q] {X : Matrix m p 𝕜}
    {Y : Matrix p q 𝕜} {Z : 𝕜 → Matrix q r 𝕜} (hZ : ∀ k l, ContinuousAt (fun s => Z s k l) 0)
    (i : m) (j : r) : ContinuousAt (fun s => (X * Y * Z s) i j) 0 := by
  simp only [Matrix.mul_apply]
  exact tendsto_finsetSum _ fun k _ => continuousAt_const.mul (hZ k j)

/-- **With a source, `∂_J S = L K_a R`** at `J = 0`, entry by entry. -/
theorem schur_source_deriv (A Aa : Matrix m m 𝕜) (B Ba : Matrix m n 𝕜) (C Ca : Matrix n m 𝕜)
    (D Da : Matrix n n 𝕜) (hD : D.det ≠ 0) (i j : m) :
    HasDerivAt (fun s : 𝕜 => schurN (A + s • Aa) (B + s • Ba) (C + s • Ca) (D + s • Da) i j)
      ((schurLN B D * fromBlocks Aa Ba Ca Da * schurRN C D) i j) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hR := continuousAt_entry_mul (X := schurLN B D) (Y := fromBlocks Aa Ba Ca Da)
    (continuousAt_schurRN_entry C Ca D Da hD) i j
  have hlim : Tendsto (fun s : 𝕜 =>
      (schurLN B D * fromBlocks Aa Ba Ca Da * schurRN (C + s • Ca) (D + s • Da)) i j)
      (𝓝[≠] 0) (𝓝 ((schurLN B D * fromBlocks Aa Ba Ca Da * schurRN C D) i j)) := by
    have := hR.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using this
  refine hlim.congr' ?_
  have hev := (eventually_det_ne D Da hD).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hs0
  have hdiff := schurN_diff (A := A) (A' := A + s • Aa) (B := B) (B' := B + s • Ba) (C := C)
    (C' := C + s • Ca) hD hs
  rw [fromBlocks_source, Matrix.mul_smul, Matrix.smul_mul] at hdiff
  have hs0' : s ≠ 0 := hs0
  rw [slope_def_field, sub_zero]
  have e := congrFun (congrFun hdiff i) j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, zero_smul, add_zero] at e ⊢
  rw [e]
  field_simp

/-- **The derivative of `L` along a source:** `∂L = −L K_a Q`, entry by entry. -/
theorem schurLN_deriv (A Aa : Matrix m m 𝕜) (B Ba : Matrix m n 𝕜) (C Ca : Matrix n m 𝕜)
    (D Da : Matrix n n 𝕜) (hD : D.det ≠ 0) (i : m) (k : m ⊕ n) :
    HasDerivAt (fun s : 𝕜 => schurLN (B + s • Ba) (D + s • Da) i k)
      (-(schurLN B D * fromBlocks Aa Ba Ca Da * schurQN (m := m) D) i k) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hQ : ContinuousAt (fun s : 𝕜 =>
      (schurLN B D * fromBlocks Aa Ba Ca Da * schurQN (m := m) (D + s • Da)) i k) 0 :=
    continuousAt_entry_mul (continuousAt_schurQN_entry D Da hD) i k
  have hlim : Tendsto (fun s : 𝕜 =>
      -(schurLN B D * fromBlocks Aa Ba Ca Da * schurQN (m := m) (D + s • Da)) i k)
      (𝓝[≠] 0) (𝓝 (-(schurLN B D * fromBlocks Aa Ba Ca Da * schurQN (m := m) D) i k)) := by
    have := (hQ.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).neg
    simpa using this
  refine hlim.congr' ?_
  have hev := (eventually_det_ne D Da hD).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hs0
  have hdiff := schurLN_diff (A := A) (A' := A + s • Aa) (B := B) (B' := B + s • Ba) (C := C)
    (C' := C + s • Ca) hD hs
  rw [fromBlocks_source, Matrix.mul_smul, Matrix.smul_mul] at hdiff
  have hs0' : s ≠ 0 := hs0
  rw [slope_def_field, sub_zero]
  have e := congrFun (congrFun hdiff i) k
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, zero_smul,
    add_zero] at e ⊢
  rw [e]
  field_simp

/-- **The derivative of `R` along a source:** `∂R = −Q K_a R`, entry by entry. -/
theorem schurRN_deriv (A Aa : Matrix m m 𝕜) (B Ba : Matrix m n 𝕜) (C Ca : Matrix n m 𝕜)
    (D Da : Matrix n n 𝕜) (hD : D.det ≠ 0) (k : m ⊕ n) (j : m) :
    HasDerivAt (fun s : 𝕜 => schurRN (C + s • Ca) (D + s • Da) k j)
      (-(schurQN (m := m) D * fromBlocks Aa Ba Ca Da * schurRN C D) k j) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hR : ContinuousAt (fun s : 𝕜 =>
      (schurQN (m := m) D * fromBlocks Aa Ba Ca Da * schurRN (C + s • Ca) (D + s • Da)) k j) 0 :=
    continuousAt_entry_mul (continuousAt_schurRN_entry C Ca D Da hD) k j
  have hlim : Tendsto (fun s : 𝕜 =>
      -(schurQN (m := m) D * fromBlocks Aa Ba Ca Da * schurRN (C + s • Ca) (D + s • Da)) k j)
      (𝓝[≠] 0) (𝓝 (-(schurQN (m := m) D * fromBlocks Aa Ba Ca Da * schurRN C D) k j)) := by
    have := (hR.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).neg
    simpa using this
  refine hlim.congr' ?_
  have hev := (eventually_det_ne D Da hD).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hs0
  have hdiff := schurRN_diff (A := A) (A' := A + s • Aa) (B := B) (B' := B + s • Ba) (C := C)
    (C' := C + s • Ca) hD hs
  rw [fromBlocks_source, Matrix.mul_smul, Matrix.smul_mul] at hdiff
  have hs0' : s ≠ 0 := hs0
  rw [slope_def_field, sub_zero]
  have e := congrFun (congrFun hdiff k) j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, zero_smul,
    add_zero] at e ⊢
  rw [e]
  field_simp

/-- An entry of a triple product, as a double sum. -/
theorem entry_mul3 {p q : Type*} [Fintype p] [Fintype q] (X : Matrix m p 𝕜) (Y : Matrix p q 𝕜)
    (Z : Matrix q m 𝕜) (i j : m) : (X * Y * Z) i j = ∑ k, ∑ l, X i k * Y k l * Z l j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **With two sources, `∂_s∂_t S = L(K_ab − K_aQK_b − K_bQK_a)R`** at `s = t = 0`, for
`K(s, t) = K + sK_a + t(K_b + sK_ab)`, entry by entry. -/
theorem schur_source_mixed (A Aa Ab Aab : Matrix m m 𝕜) (B Ba Bb Bab : Matrix m n 𝕜)
    (C Ca Cb Cab : Matrix n m 𝕜) (D Da Db Dab : Matrix n n 𝕜) (hD : D.det ≠ 0) (i j : m) :
    HasDerivAt (fun s : 𝕜 => deriv (fun t : 𝕜 =>
        schurN (A + s • Aa + t • (Ab + s • Aab)) (B + s • Ba + t • (Bb + s • Bab))
          (C + s • Ca + t • (Cb + s • Cab)) (D + s • Da + t • (Db + s • Dab)) i j) 0)
      ((schurLN B D * (fromBlocks Aab Bab Cab Dab -
          fromBlocks Aa Ba Ca Da * schurQN (m := m) D * fromBlocks Ab Bb Cb Db -
          fromBlocks Ab Bb Cb Db * schurQN (m := m) D * fromBlocks Aa Ba Ca Da) * schurRN C D) i j) 0 := by
  -- the first derivative in `t`, for every `s` near `0`
  have hfirst : ∀ᶠ s in 𝓝 (0 : 𝕜), (fun s => ∑ k, ∑ l, schurLN (B + s • Ba) (D + s • Da) i k *
        fromBlocks (Ab + s • Aab) (Bb + s • Bab) (Cb + s • Cab) (Db + s • Dab) k l *
          schurRN (C + s • Ca) (D + s • Da) l j) s =
      deriv (fun t : 𝕜 =>
        schurN (A + s • Aa + t • (Ab + s • Aab)) (B + s • Ba + t • (Bb + s • Bab))
          (C + s • Ca + t • (Cb + s • Cab)) (D + s • Da + t • (Db + s • Dab)) i j) 0 := by
    filter_upwards [eventually_det_ne D Da hD] with s hs
    rw [(schur_source_deriv (A + s • Aa) (Ab + s • Aab) (B + s • Ba) (Bb + s • Bab) (C + s • Ca)
      (Cb + s • Cab) (D + s • Da) (Db + s • Dab) hs i j).deriv, entry_mul3]
  refine HasDerivAt.congr_of_eventuallyEq ?_ (Filter.EventuallyEq.symm hfirst)
  -- the product rule on the double sum
  have hL := fun k => schurLN_deriv A Aa B Ba C Ca D Da hD i k
  have hR := fun l => schurRN_deriv A Aa B Ba C Ca D Da hD l j
  have hK : ∀ k l, HasDerivAt (fun s : 𝕜 =>
      fromBlocks (Ab + s • Aab) (Bb + s • Bab) (Cb + s • Cab) (Db + s • Dab) k l)
      (fromBlocks Aab Bab Cab Dab k l) 0 := by
    intro k l
    have e : (fun s : 𝕜 => fromBlocks (Ab + s • Aab) (Bb + s • Bab) (Cb + s • Cab) (Db + s • Dab) k l) =
        fun s => fromBlocks Ab Bb Cb Db k l + s * fromBlocks Aab Bab Cab Dab k l := by
      funext s
      rcases k with a | b <;> rcases l with c | d <;> simp
    rw [e]
    simpa using ((hasDerivAt_id (0 : 𝕜)).mul_const (fromBlocks Aab Bab Cab Dab k l)).const_add
      (fromBlocks Ab Bb Cb Db k l)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun l _ => ((hL k).mul (hK k l)).mul (hR l)
  have hval : (schurLN B D * (fromBlocks Aab Bab Cab Dab -
        fromBlocks Aa Ba Ca Da * schurQN (m := m) D * fromBlocks Ab Bb Cb Db -
        fromBlocks Ab Bb Cb Db * schurQN (m := m) D * fromBlocks Aa Ba Ca Da) * schurRN C D) i j =
      ∑ k, ∑ l, ((-(schurLN B D * fromBlocks Aa Ba Ca Da * schurQN (m := m) D) i k *
          fromBlocks Ab Bb Cb Db k l + schurLN B D i k * fromBlocks Aab Bab Cab Dab k l) *
            schurRN C D l j + schurLN B D i k * fromBlocks Ab Bb Cb Db k l *
              (-(schurQN (m := m) D * fromBlocks Aa Ba Ca Da * schurRN C D) l j)) := by
    rw [show schurLN B D * (fromBlocks Aab Bab Cab Dab -
          fromBlocks Aa Ba Ca Da * schurQN (m := m) D * fromBlocks Ab Bb Cb Db -
          fromBlocks Ab Bb Cb Db * schurQN (m := m) D * fromBlocks Aa Ba Ca Da) * schurRN C D =
        schurLN B D * fromBlocks Aab Bab Cab Dab * schurRN C D -
          (schurLN B D * fromBlocks Aa Ba Ca Da * schurQN (m := m) D) * fromBlocks Ab Bb Cb Db *
            schurRN C D -
          schurLN B D * fromBlocks Ab Bb Cb Db *
            (schurQN (m := m) D * fromBlocks Aa Ba Ca Da * schurRN C D) by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]]
    rw [Matrix.sub_apply, Matrix.sub_apply, entry_mul3, entry_mul3, entry_mul3,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hval]
  convert hsum using 1 <;> simp only [Pi.mul_apply, zero_smul, add_zero]

end Schur

section Pole

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The residue at a simple zero of a determinant, over any nontrivially normed field: if `K` is continuous
at `u₀`, `det K(u₀) = 0` and `det K` has the derivative `d ≠ 0` at `u₀`, then `(u − u₀)K(u)⁻¹ → adj K(u₀)/d`. -/
theorem residue_general_field (K : 𝕜 → Matrix ι ι 𝕜) (u₀ d : 𝕜) (hK : ContinuousAt K u₀)
    (h0 : (K u₀).det = 0) (hd : HasDerivAt (fun u => (K u).det) d u₀) (hd0 : d ≠ 0) :
    Tendsto (fun u => (u - u₀) • (K u)⁻¹) (𝓝[≠] u₀) (𝓝 (d⁻¹ • (K u₀).adjugate)) := by
  have hslope := hd.tendsto_slope
  have hadj : Tendsto (fun u => (K u).adjugate) (𝓝[≠] u₀) (𝓝 (K u₀).adjugate) := by
    have hc : ContinuousAt (fun u => (K u).adjugate) u₀ := by
      have := (continuous_id.matrix_adjugate (n := ι) (R := 𝕜)).continuousAt (x := K u₀)
      exact this.comp hK
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun u => (slope (fun u => (K u).det) u₀ u)⁻¹) (𝓝[≠] u₀) (𝓝 d⁻¹) :=
    hslope.inv₀ hd0
  have hprod := hinv.smul hadj
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [slope_def_field, h0, sub_zero, inv_div, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv',
    div_eq_mul_inv]

/-- **The residue at a simple zero** `ζ₀` of `det S`, with the kernels spanned by `r` and `ℓ`:
`ℓ S_ζ r ≠ 0` and `(ζ − ζ₀) S(ζ)⁻¹ → r ℓᵀ/(ℓ S_ζ r)`. -/
theorem residue_at_simple_zero (S : 𝕜 → Matrix ι ι 𝕜) (ζ₀ : 𝕜) (Sζ : Matrix ι ι 𝕜)
    (hS : ∀ i j, HasDerivAt (fun ζ => S ζ i j) (Sζ i j) ζ₀) (hdet : (S ζ₀).det = 0)
    (r ℓ : ι → 𝕜) (hr : r ≠ 0) (hkerR : ∀ v, S ζ₀ *ᵥ v = 0 → ∃ c : 𝕜, v = c • r)
    (hkerL : ∀ w, w ᵥ* S ζ₀ = 0 → ∃ c : 𝕜, w = c • ℓ)
    (hsimple : deriv (fun ζ => (S ζ).det) ζ₀ ≠ 0) :
    ℓ ⬝ᵥ (Sζ *ᵥ r) ≠ 0 ∧
      Tendsto (fun ζ => (ζ - ζ₀) • (S ζ)⁻¹) (𝓝[≠] ζ₀) (𝓝 ((ℓ ⬝ᵥ (Sζ *ᵥ r))⁻¹ • vecMulVec r ℓ)) := by
  have hd := hasDerivAt_det hS
  obtain ⟨κ, hκ⟩ := adjugate_rank_one (S ζ₀) r ℓ hr hdet hkerR hkerL
  have hdval : ((S ζ₀).adjugate * Sζ).trace = κ * (ℓ ⬝ᵥ (Sζ *ᵥ r)) := by
    rw [hκ, trace_smul_vecMulVec_mul]
  have hd0 : ((S ζ₀).adjugate * Sζ).trace ≠ 0 := by rwa [← hd.deriv]
  have hκ0 : κ ≠ 0 := by
    intro h; apply hd0; rw [hdval, h, zero_mul]
  have hℓ0 : ℓ ⬝ᵥ (Sζ *ᵥ r) ≠ 0 := by
    intro h; apply hd0; rw [hdval, h, mul_zero]
  have hcont : ContinuousAt S ζ₀ :=
    continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => (hS i j).continuousAt
  have hres := residue_general_field S ζ₀ _ hcont hdet hd hd0
  refine ⟨hℓ0, ?_⟩
  convert hres using 2
  rw [hκ, trace_smul_vecMulVec_mul, smul_smul]
  congr 1
  field_simp

end Pole

section Shift

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of the pencil `S(ζ, J) = S₀ + (ζ − ζ₀)S_ζ + J S_a`. -/
noncomputable def pencilDet (S₀ Sζ Sa : Matrix ι ι 𝕜) (ζ₀ J ζ : 𝕜) : 𝕜 :=
  (S₀ + (ζ - ζ₀) • Sζ + J • Sa).det

theorem pencilDet_hasDerivAt_J (S₀ Sζ Sa : Matrix ι ι 𝕜) (ζ₀ J ζ : 𝕜) :
    HasDerivAt (fun J => pencilDet S₀ Sζ Sa ζ₀ J ζ)
      ((S₀ + (ζ - ζ₀) • Sζ + J • Sa).adjugate * Sa).trace J := by
  apply hasDerivAt_det
  intro i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simpa using ((hasDerivAt_id J).mul_const (Sa i j)).const_add (S₀ i j + (ζ - ζ₀) * Sζ i j)

theorem pencilDet_hasDerivAt_ζ (S₀ Sζ Sa : Matrix ι ι 𝕜) (ζ₀ J ζ : 𝕜) :
    HasDerivAt (fun ζ => pencilDet S₀ Sζ Sa ζ₀ J ζ)
      ((S₀ + (ζ - ζ₀) • Sζ + J • Sa).adjugate * Sζ).trace ζ := by
  apply hasDerivAt_det
  intro i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have h := (((hasDerivAt_id ζ).sub_const ζ₀).mul_const (Sζ i j)).const_add (S₀ i j)
  simpa using h.add_const (J * Sa i j)

theorem pencil_adj_continuous (S₀ Sζ Sa : Matrix ι ι 𝕜) (ζ₀ : 𝕜) :
    Continuous (fun p : 𝕜 × 𝕜 => (S₀ + (p.2 - ζ₀) • Sζ + p.1 • Sa).adjugate) := by
  apply Continuous.matrix_adjugate
  exact (continuous_const.add ((continuous_snd.sub continuous_const).smul continuous_const)).add
    (continuous_fst.smul continuous_const)

/-- **The shift of a simple zero under a source:** for the pencil `S(ζ, J) = S₀ + (ζ − ζ₀)S_ζ + J S_a`, with
`det S₀ = 0`, the kernels of `S₀` spanned by `r` and `ℓ`, and `ζ₀` a simple zero (`∂_ζ det S = tr(adj S₀ S_ζ) ≠ 0`),
the zero `ζ(J)` of `det S(·, J)` through `ζ(0) = ζ₀` exists near `J = 0` and `dζ/dJ = −ℓ S_a r/(ℓ S_ζ r)`, over
`ℝ` and over `ℂ` (every `RCLike` field: the implicit function theorem holds there). -/
theorem zero_shift_pencil (S₀ Sζ Sa : Matrix ι ι 𝕜) (ζ₀ : 𝕜) (r ℓ : ι → 𝕜) (hr : r ≠ 0)
    (hdet : S₀.det = 0) (hkerR : ∀ v, S₀ *ᵥ v = 0 → ∃ c : 𝕜, v = c • r)
    (hkerL : ∀ w, w ᵥ* S₀ = 0 → ∃ c : 𝕜, w = c • ℓ) (hsimple : (S₀.adjugate * Sζ).trace ≠ 0) :
    ℓ ⬝ᵥ (Sζ *ᵥ r) ≠ 0 ∧
    ∃ ζ : 𝕜 → 𝕜, ζ 0 = ζ₀ ∧ (∀ᶠ J in 𝓝 0, pencilDet S₀ Sζ Sa ζ₀ J (ζ J) = 0) ∧
      HasDerivAt ζ (-(ℓ ⬝ᵥ (Sa *ᵥ r)) / (ℓ ⬝ᵥ (Sζ *ᵥ r))) 0 := by
  obtain ⟨κ, hκ⟩ := adjugate_rank_one S₀ r ℓ hr hdet hkerR hkerL
  have hval : ∀ M : Matrix ι ι 𝕜, (S₀.adjugate * M).trace = κ * (ℓ ⬝ᵥ (M *ᵥ r)) := by
    intro M; rw [hκ, trace_smul_vecMulVec_mul]
  have hκ0 : κ ≠ 0 := by intro h; apply hsimple; rw [hval, h, zero_mul]
  have hℓ0 : ℓ ⬝ᵥ (Sζ *ᵥ r) ≠ 0 := by intro h; apply hsimple; rw [hval, h, mul_zero]
  refine ⟨hℓ0, ?_⟩
  have h00 : S₀ + (ζ₀ - ζ₀) • Sζ + (0 : 𝕜) • Sa = S₀ := by simp
  let fJ : 𝕜 → 𝕜 → 𝕜 := fun J ζ => ((S₀ + (ζ - ζ₀) • Sζ + J • Sa).adjugate * Sa).trace
  let fζ : 𝕜 → 𝕜 → 𝕜 := fun J ζ => ((S₀ + (ζ - ζ₀) • Sζ + J • Sa).adjugate * Sζ).trace
  have hU : fζ 0 ζ₀ = κ * (ℓ ⬝ᵥ (Sζ *ᵥ r)) := by
    show ((S₀ + (ζ₀ - ζ₀) • Sζ + (0 : 𝕜) • Sa).adjugate * Sζ).trace = _
    rw [h00]; exact hval Sζ
  have hJ : fJ 0 ζ₀ = κ * (ℓ ⬝ᵥ (Sa *ᵥ r)) := by
    show ((S₀ + (ζ₀ - ζ₀) • Sζ + (0 : 𝕜) • Sa).adjugate * Sa).trace = _
    rw [h00]; exact hval Sa
  have hU0 : fζ 0 ζ₀ ≠ 0 := by rw [hU]; exact mul_ne_zero hκ0 hℓ0
  have df₁ : ∀ᶠ w in 𝓝 ((0 : 𝕜), ζ₀), HasFDerivAt (pencilDet S₀ Sζ Sa ζ₀ · w.2)
      ((fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fJ J ζ)) w.1 w.2) w.1 :=
    Filter.Eventually.of_forall fun w => (pencilDet_hasDerivAt_J S₀ Sζ Sa ζ₀ w.1 w.2).hasFDerivAt
  have df₂ : ∀ᶠ w in 𝓝 ((0 : 𝕜), ζ₀), HasFDerivAt (pencilDet S₀ Sζ Sa ζ₀ w.1 ·)
      ((fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fζ J ζ)) w.1 w.2) w.2 :=
    Filter.Eventually.of_forall fun w => (pencilDet_hasDerivAt_ζ S₀ Sζ Sa ζ₀ w.1 w.2).hasFDerivAt
  have cJ : Continuous (fun p : 𝕜 × 𝕜 => fJ p.1 p.2) :=
    ((pencil_adj_continuous S₀ Sζ Sa ζ₀).mul continuous_const).matrix_trace
  have cU : Continuous (fun p : 𝕜 × 𝕜 => fζ p.1 p.2) :=
    ((pencil_adj_continuous S₀ Sζ Sa ζ₀).mul continuous_const).matrix_trace
  have cf₁ : ContinuousAt
      (Function.uncurry fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fJ J ζ)) ((0 : 𝕜), ζ₀) :=
    ((ContinuousLinearMap.toSpanSingletonLIE 𝕜 𝕜).continuous.comp cJ).continuousAt
  have cf₂ : ContinuousAt
      (Function.uncurry fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fζ J ζ)) ((0 : 𝕜), ζ₀) :=
    ((ContinuousLinearMap.toSpanSingletonLIE 𝕜 𝕜).continuous.comp cU).continuousAt
  have if₂u : ((fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fζ J ζ))
      ((0 : 𝕜), ζ₀).1 ((0 : 𝕜), ζ₀).2).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.toSpanSingleton 𝕜 (fζ 0 ζ₀)⁻¹) ?_ ?_
    · ext
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, one_mul, ContinuousLinearMap.id_apply]
      exact inv_mul_cancel₀ hU0
    · ext
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, one_mul, ContinuousLinearMap.id_apply]
      exact mul_inv_cancel₀ hU0
  let ζf := implicitFunctionOfBivariate (u := ((0 : 𝕜), ζ₀)) (f := pencilDet S₀ Sζ Sa ζ₀)
    (f₁ := fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fJ J ζ))
    (f₂ := fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fζ J ζ))
    df₁ df₂ cf₁ cf₂ if₂u
  have hζ0 : ζf 0 = ζ₀ := by
    have := (eventually_apply_eq_iff_implicitFunctionOfBivariate (u := ((0 : 𝕜), ζ₀))
      (f := pencilDet S₀ Sζ Sa ζ₀)
      (f₁ := fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fJ J ζ))
      (f₂ := fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fζ J ζ))
      df₁ df₂ cf₁ cf₂ if₂u).self_of_nhds
    exact this.mp rfl
  have hzero : ∀ᶠ J in 𝓝 (0 : 𝕜), pencilDet S₀ Sζ Sa ζ₀ J (ζf J) = 0 := by
    have := eventually_apply_implicitFunctionOfBivariate (u := ((0 : 𝕜), ζ₀))
      (f := pencilDet S₀ Sζ Sa ζ₀)
      (f₁ := fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fJ J ζ))
      (f₂ := fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fζ J ζ))
      df₁ df₂ cf₁ cf₂ if₂u
    have h0 : pencilDet S₀ Sζ Sa ζ₀ 0 ζ₀ = 0 := by
      rw [pencilDet, h00]
      exact hdet
    filter_upwards [this] with J hJ'
    rw [hJ']
    exact h0
  have hderiv := (hasStrictFDerivAt_implicitFunctionOfBivariate (u := ((0 : 𝕜), ζ₀))
    (f := pencilDet S₀ Sζ Sa ζ₀)
    (f₁ := fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fJ J ζ))
    (f₂ := fun J ζ => ContinuousLinearMap.toSpanSingleton 𝕜 (fζ J ζ))
    df₁ df₂ cf₁ cf₂ if₂u).hasFDerivAt
  refine ⟨ζf, hζ0, hzero, ?_⟩
  have h1 := hderiv.hasDerivAt
  convert h1 using 1
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  have hinv : (ContinuousLinearMap.toSpanSingleton 𝕜 (fζ 0 ζ₀)).inverse (fJ 0 ζ₀) =
      fJ 0 ζ₀ / fζ 0 ζ₀ := by
    rw [if₂u.inverse_apply_eq]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    field_simp
  rw [hinv, hJ, hU]
  field_simp

end Shift

end Law

open Comparison.System.Law

/-- **Proposition 57, closing a level.** For `K = [[A, B], [C, D]]` with `D` invertible and
`S = A − BD⁻¹C`: `det K = det D · det S` and `K⁻¹ = RS⁻¹L + Q`; with a source `K + sK_a`, `∂_sS = LK_aR`;
with two sources `K + sK_a + t(K_b + sK_ab)`, `∂_s∂_tS = L(K_ab − K_aQK_b − K_bQK_a)R`; at a simple zero
`ζ₀` of `det S` with `Sr = 0 = ℓS` (kernels spanned by `r`, `ℓ`): `ℓS_ζr ≠ 0` and
`Res S⁻¹ = lim (ζ − ζ₀)S(ζ)⁻¹ = rℓᵀ/(ℓS_ζr)`; and for the pencil `S₀ + (ζ − ζ₀)S_ζ + JS_a`,
`dζ₀/dJ = −ℓS_ar/(ℓS_ζr)` over `ℝ` and over `ℂ` (every `RCLike` field), the law's reduced operators being
complex. -/
theorem prop_57 :
    (∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ) [Invertible D],
      (fromBlocks A B C D).det = D.det * (schurS A B C D).det ∧
      ∀ [Invertible (schurS A B C D)],
        (fromBlocks A B C D)⁻¹ = schurR C D * ⅟(schurS A B C D) * schurL B D + schurQ D) ∧
    (∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (A Aa : Matrix m m ℂ) (B Ba : Matrix m n ℂ) (C Ca : Matrix n m ℂ) (D Da : Matrix n n ℂ),
      D.det ≠ 0 → ∀ i j : m,
      HasDerivAt (fun s : ℂ => schurN (A + s • Aa) (B + s • Ba) (C + s • Ca) (D + s • Da) i j)
        ((schurLN B D * fromBlocks Aa Ba Ca Da * schurRN C D) i j) 0) ∧
    (∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (A Aa Ab Aab : Matrix m m ℂ) (B Ba Bb Bab : Matrix m n ℂ) (C Ca Cb Cab : Matrix n m ℂ)
        (D Da Db Dab : Matrix n n ℂ), D.det ≠ 0 → ∀ i j : m,
      HasDerivAt (fun s : ℂ => deriv (fun t : ℂ =>
          schurN (A + s • Aa + t • (Ab + s • Aab)) (B + s • Ba + t • (Bb + s • Bab))
            (C + s • Ca + t • (Cb + s • Cab)) (D + s • Da + t • (Db + s • Dab)) i j) 0)
        ((schurLN B D * (fromBlocks Aab Bab Cab Dab -
            fromBlocks Aa Ba Ca Da * schurQN (m := m) D * fromBlocks Ab Bb Cb Db -
            fromBlocks Ab Bb Cb Db * schurQN (m := m) D * fromBlocks Aa Ba Ca Da) * schurRN C D) i j) 0) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ℂ → Matrix ι ι ℂ) (ζ₀ : ℂ) (Sζ : Matrix ι ι ℂ),
      (∀ i j, HasDerivAt (fun ζ => S ζ i j) (Sζ i j) ζ₀) → (S ζ₀).det = 0 →
      ∀ (r ℓ : ι → ℂ), r ≠ 0 → (∀ v, S ζ₀ *ᵥ v = 0 → ∃ c : ℂ, v = c • r) →
      (∀ w, w ᵥ* S ζ₀ = 0 → ∃ c : ℂ, w = c • ℓ) → deriv (fun ζ => (S ζ).det) ζ₀ ≠ 0 →
      ℓ ⬝ᵥ (Sζ *ᵥ r) ≠ 0 ∧
        Tendsto (fun ζ => (ζ - ζ₀) • (S ζ)⁻¹) (𝓝[≠] ζ₀)
          (𝓝 ((ℓ ⬝ᵥ (Sζ *ᵥ r))⁻¹ • vecMulVec r ℓ))) ∧
    (∀ (𝕜 : Type) [RCLike 𝕜] (ι : Type) [Fintype ι] [DecidableEq ι] (S₀ Sζ Sa : Matrix ι ι 𝕜) (ζ₀ : 𝕜)
      (r ℓ : ι → 𝕜),
      r ≠ 0 → S₀.det = 0 → (∀ v, S₀ *ᵥ v = 0 → ∃ c : 𝕜, v = c • r) →
      (∀ w, w ᵥ* S₀ = 0 → ∃ c : 𝕜, w = c • ℓ) → (S₀.adjugate * Sζ).trace ≠ 0 →
      ℓ ⬝ᵥ (Sζ *ᵥ r) ≠ 0 ∧
      ∃ ζ : 𝕜 → 𝕜, ζ 0 = ζ₀ ∧ (∀ᶠ J in 𝓝 0, (S₀ + (ζ J - ζ₀) • Sζ + J • Sa).det = 0) ∧
        HasDerivAt ζ (-(ℓ ⬝ᵥ (Sa *ᵥ r)) / (ℓ ⬝ᵥ (Sζ *ᵥ r))) 0) :=
  ⟨fun m n _ _ _ _ A B C D _ => ⟨schur_det A B C D, fun {_} => schur_inv A B C D⟩,
    fun m n _ _ _ _ A Aa B Ba C Ca D Da hD i j => schur_source_deriv A Aa B Ba C Ca D Da hD i j,
    fun m n _ _ _ _ A Aa Ab Aab B Ba Bb Bab C Ca Cb Cab D Da Db Dab hD i j =>
      schur_source_mixed A Aa Ab Aab B Ba Bb Bab C Ca Cb Cab D Da Db Dab hD i j,
    fun ι _ _ S ζ₀ Sζ hS hdet r ℓ hr hR hL hs => residue_at_simple_zero S ζ₀ Sζ hS hdet r ℓ hr hR hL hs,
    fun 𝕜 _ ι _ _ S₀ Sζ Sa ζ₀ r ℓ hr hdet hR hL hs => zero_shift_pencil S₀ Sζ Sa ζ₀ r ℓ hr hdet hR hL hs⟩

end Comparison.System
