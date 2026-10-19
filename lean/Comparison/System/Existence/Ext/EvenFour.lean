module

public import Comparison.System.Existence.Ext.Covariance
public import Comparison.Elements.Observables

/-
A copy of `Comparison/Existence/EvenFour.lean`
(commit 3b95f8b), changed only in its namespace (`Comparison` to `Comparison.SysExt`) and in the import
paths of the copied files. The original cannot enter the root `Comparison.System`: `Existence/Exterior.lean`
declares `Comparison.volume` and `Comparison.half_mul_self`, as do `Colour/GramTerm.lean` and
`Elements/Half.lean`.
-/

/-!
# Book VII. The even words of the step are all the operators of the four amplitudes
(Proposition 37)

The six with their lengths are
`Q6(v) = Σ_a v_a²` on `ℝ⁶` (direction `0` the singlet `n`, directions `1, …, 5` the five directions). Mathlib's
`CliffordAlgebra Q6` is the algebra of the vertical steps, `cl a = ι(e_a)`, and its even part
`CliffordAlgebra.even Q6` the algebra of the even words.

* `rhoL v = v₀ + iΓ(v)`, `sigmaL v = v₀ − iΓ(v)`, `Γ(v) = Σ_t v_{t+1} γ_t`: `ρ(v)σ(v) = σ(v)ρ(v) = Q6(v)`
  (`rho_sigma`, `sigma_rho`), so `(u, v) ↦ ρ(u)σ(v)` is an `EvenHom` and lifts to the real algebra
  homomorphism `evenToFour : even Q6 →ₐ[ℝ] Matrix Four Four ℂ`.
* `evenToFour_singlet_line`: **`J_nJ_t ↦ −iγ_t`**; `evenToFour_line_line`: **`J_sJ_t ↦ γ_sγ_t`**;
  `line_eq_i_singlet_line`: **`γ_t = i · (image of J_nJ_t)`**.
* `evenToFour_surjective`: every operator of the four amplitudes is reached.
* `even_le_span`: the even part is spanned by the 32 ordered even words (`clWord`);
  `evenToFour_injective`, `evenToFour_bijective`, `evenEquivFour`: **an isomorphism of real algebras
  from the even Clifford algebra of the six onto all operators of the four amplitudes.**
* `stepRep`: `ι(v) ↦ J(v)` lifts to `CliffordAlgebra Q6 →ₐ[ℝ] Module.End ℝ (Finset (Fin 6) → ℝ)`,
  `stepRep_cl`: `cl a ↦ J_a`; `stepRep_injective`: faithful, since the word of `S` takes `f_∅` to `f_S`.
  So the even words of the vertical step `J` on the sixty-four sets are the even Clifford algebra,
  and through `evenEquivFour` all operators of the four amplitudes.
-/

@[expose] public section

namespace Comparison.SysExt

open Finset
open scoped Matrix

/-! ## The six as a quadratic space and its Clifford algebra -/

section Six

/-- **The six with their lengths:** `Q6(v) = Σ_a v_a²`. -/
noncomputable def Q6 : QuadraticForm ℝ (Fin 6 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun _ : Fin 6 => (1 : ℝ))

theorem Q6_apply (v : Fin 6 → ℝ) : Q6 v = ∑ a, v a * v a := by
  simp [Q6]

/-- The direction `a` of the six. -/
def e6 (a : Fin 6) : Fin 6 → ℝ := Pi.single a 1

theorem Q6_e6 (a : Fin 6) : Q6 (e6 a) = 1 := by
  rw [Q6_apply]
  simp [e6, Pi.single_apply]

theorem polar_e6 {a b : Fin 6} (hab : a ≠ b) : QuadraticMap.polar Q6 (e6 a) (e6 b) = 0 := by
  rw [QuadraticMap.polar, Q6_apply, Q6_e6, Q6_e6]
  have : ∑ i : Fin 6, (e6 a + e6 b) i * (e6 a + e6 b) i = 2 := by
    simp only [e6, Pi.add_apply, Pi.single_apply]
    fin_cases a <;> fin_cases b <;> simp_all [Fin.sum_univ_six] <;> norm_num
  rw [this]
  norm_num

/-- **The vertical step along the direction `a`**, in the Clifford algebra: `cl a = ι(e_a)`. -/
noncomputable def cl (a : Fin 6) : CliffordAlgebra Q6 := CliffordAlgebra.ι Q6 (e6 a)

theorem cl_sq (a : Fin 6) : cl a * cl a = 1 := by
  rw [cl, CliffordAlgebra.ι_sq_scalar, Q6_e6, map_one]

theorem cl_anti {a b : Fin 6} (hab : a ≠ b) : cl a * cl b = -(cl b * cl a) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q6) (e6 a) (e6 b)
  rw [polar_e6 hab, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem ι_eq_sum_cl (m : Fin 6 → ℝ) : CliffordAlgebra.ι Q6 m = ∑ a, m a • cl a := by
  conv_lhs => rw [vec_eq_sum m]
  rw [map_sum]
  simp only [map_smul, cl, e6]

/-- The ordered word `cl_{s₁} ⋯ cl_{s_r}` of a set `S`. -/
noncomputable def clWord (S : Finset (Fin 6)) : CliffordAlgebra Q6 := ordProd cl S

theorem cl_mul_clWord (a : Fin 6) (S : Finset (Fin 6)) :
    cl a * clWord S = (-1) ^ (S.filter (· < a)).card *
      (if a ∈ S then clWord (S.erase a) else clWord (insert a S)) := by
  have h := ordProd_mul_left cl (fun _ => 1) (fun a b hab => cl_anti hab) cl_sq
    (fun _ _ => Commute.one_left _) S a
  simp only [one_mul] at h
  exact h

theorem neg_one_pow_mul_eq_smul {A : Type*} [Ring A] [Algebra ℝ A] (k : ℕ) (x : A) :
    (-1 : A) ^ k * x = ((-1 : ℝ) ^ k) • x := by
  rw [Algebra.smul_def, map_pow, map_neg, map_one]

/-- The word of `S` lies in the part of parity `|S|`. -/
theorem clWord_mem_evenOdd (S : Finset (Fin 6)) :
    clWord S ∈ CliffordAlgebra.evenOdd Q6 (S.card : ZMod 2) := by
  induction S using Finset.induction_on_min with
  | empty =>
    simp only [clWord, ordProd_empty, Finset.card_empty, Nat.cast_zero]
    exact SetLike.one_mem_graded _
  | insert m S hm ih =>
    have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
    rw [clWord, ordProd_insert_min cl hm, Finset.card_insert_of_notMem hmS, Nat.cast_succ,
      add_comm]
    exact SetLike.mul_mem_graded (CliffordAlgebra.ι_mem_evenOdd_one Q6 (e6 m)) ih

/-- The even sets of the six: 32 of them. -/
abbrev EvenSets := {S : Finset (Fin 6) // Even S.card}

/-- The odd sets of the six. -/
abbrev OddSets := {S : Finset (Fin 6) // ¬Even S.card}

theorem card_evenSets : Fintype.card EvenSets = 32 := by
  decide

theorem clWord_mem_even (S : EvenSets) : clWord S.1 ∈ CliffordAlgebra.even Q6 := by
  have h := clWord_mem_evenOdd S.1
  rwa [(ZMod.natCast_eq_zero_iff_even).mpr S.2] at h

/-- The span of the even words. -/
noncomputable def Peven : Submodule ℝ (CliffordAlgebra Q6) :=
  Submodule.span ℝ (Set.range fun S : EvenSets => clWord S.1)

/-- The span of the odd words. -/
noncomputable def Podd : Submodule ℝ (CliffordAlgebra Q6) :=
  Submodule.span ℝ (Set.range fun S : OddSets => clWord S.1)

theorem cl_mul_mem_odd (a : Fin 6) {x : CliffordAlgebra Q6} (hx : x ∈ Peven) :
    cl a * x ∈ Podd := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨S, rfl⟩ := hy
    rw [cl_mul_clWord, neg_one_pow_mul_eq_smul]
    refine Submodule.smul_mem _ _ ?_
    split_ifs with ha
    · refine Submodule.subset_span ⟨⟨S.1.erase a, ?_⟩, rfl⟩
      have h1 := Finset.card_erase_of_mem ha
      have h2 : 1 ≤ S.1.card := Finset.card_pos.mpr ⟨a, ha⟩
      have h3 := S.2
      rw [h1]
      intro h4
      obtain ⟨k, hk⟩ := h3
      obtain ⟨j, hj⟩ := h4
      omega
    · refine Submodule.subset_span ⟨⟨insert a S.1, ?_⟩, rfl⟩
      rw [Finset.card_insert_of_notMem ha]
      intro h4
      obtain ⟨k, hk⟩ := S.2
      obtain ⟨j, hj⟩ := h4
      omega
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

theorem cl_mul_mem_even (a : Fin 6) {x : CliffordAlgebra Q6} (hx : x ∈ Podd) :
    cl a * x ∈ Peven := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨S, rfl⟩ := hy
    rw [cl_mul_clWord, neg_one_pow_mul_eq_smul]
    refine Submodule.smul_mem _ _ ?_
    split_ifs with ha
    · refine Submodule.subset_span ⟨⟨S.1.erase a, ?_⟩, rfl⟩
      have h1 := Finset.card_erase_of_mem ha
      have h2 : 1 ≤ S.1.card := Finset.card_pos.mpr ⟨a, ha⟩
      rw [h1]
      rcases Nat.even_or_odd S.1.card with h3 | ⟨k, hk⟩
      · exact absurd h3 S.2
      · exact ⟨k, by omega⟩
    · refine Submodule.subset_span ⟨⟨insert a S.1, ?_⟩, rfl⟩
      rw [Finset.card_insert_of_notMem ha]
      rcases Nat.even_or_odd S.1.card with h3 | ⟨k, hk⟩
      · exact absurd h3 S.2
      · exact ⟨k + 1, by omega⟩
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

theorem ι_mul_mem_odd (m : Fin 6 → ℝ) {x : CliffordAlgebra Q6} (hx : x ∈ Peven) :
    CliffordAlgebra.ι Q6 m * x ∈ Podd := by
  rw [ι_eq_sum_cl, Finset.sum_mul]
  exact Submodule.sum_mem _ fun a _ => by
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (cl_mul_mem_odd a hx)

theorem ι_mul_mem_even (m : Fin 6 → ℝ) {x : CliffordAlgebra Q6} (hx : x ∈ Podd) :
    CliffordAlgebra.ι Q6 m * x ∈ Peven := by
  rw [ι_eq_sum_cl, Finset.sum_mul]
  exact Submodule.sum_mem _ fun a _ => by
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (cl_mul_mem_even a hx)

/-- **The even part is spanned by the 32 ordered even words.** -/
theorem even_le_span (x : CliffordAlgebra Q6) (hx : x ∈ CliffordAlgebra.even Q6) : x ∈ Peven := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨∅, by simp⟩, ?_⟩)
    simp [clWord]
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    rw [mul_assoc]
    exact ι_mul_mem_even m₁ (ι_mul_mem_odd m₂ hx)

end Six

/-! ## The map onto the four amplitudes -/

section Four

open Complex

/-- The lines of a vector of the six: `Γ(v) = Σ_t v_{t+1} γ_t`. -/
noncomputable def lineSum (v : Fin 6 → ℝ) : Matrix Four Four ℂ := ∑ t : Fin 5, ((v t.succ : ℝ) : ℂ) • γ t

/-- `ρ(v) = v₀ + iΓ(v)`. -/
noncomputable def rhoL (v : Fin 6 → ℝ) : Matrix Four Four ℂ := ((v 0 : ℝ) : ℂ) • 1 + I • lineSum v

/-- `σ(v) = v₀ − iΓ(v)`. -/
noncomputable def sigmaL (v : Fin 6 → ℝ) : Matrix Four Four ℂ := ((v 0 : ℝ) : ℂ) • 1 - I • lineSum v

theorem lineSum_sq (v : Fin 6 → ℝ) :
    lineSum v * lineSum v = ((∑ t : Fin 5, v t.succ * v t.succ : ℝ) : ℂ) • 1 := by
  rw [lineSum, sq_sum]
  push_cast
  simp only [pow_two]

theorem Q6_split (v : Fin 6 → ℝ) : Q6 v = v 0 * v 0 + ∑ t : Fin 5, v t.succ * v t.succ := by
  rw [Q6_apply, Fin.sum_univ_succ]

theorem rho_sigma (v : Fin 6 → ℝ) : rhoL v * sigmaL v = ((Q6 v : ℝ) : ℂ) • 1 := by
  have h := lineSum_sq v
  rw [Q6_split]
  simp only [rhoL, sigmaL, add_mul, mul_sub, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, h]
  rw [I_mul_I]
  push_cast
  module

theorem sigma_rho (v : Fin 6 → ℝ) : sigmaL v * rhoL v = ((Q6 v : ℝ) : ℂ) • 1 := by
  have h := lineSum_sq v
  rw [Q6_split]
  simp only [rhoL, sigmaL, sub_mul, mul_add, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, h]
  rw [I_mul_I]
  push_cast
  module

theorem lineSum_add (u w : Fin 6 → ℝ) : lineSum (u + w) = lineSum u + lineSum w := by
  simp only [lineSum, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

theorem lineSum_smul (c : ℝ) (u : Fin 6 → ℝ) : lineSum (c • u) = c • lineSum u := by
  simp only [lineSum, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  rfl

theorem rhoL_add (u w : Fin 6 → ℝ) : rhoL (u + w) = rhoL u + rhoL w := by
  simp only [rhoL, lineSum_add, Pi.add_apply, Complex.ofReal_add, add_smul, smul_add]
  abel

theorem sigmaL_add (u w : Fin 6 → ℝ) : sigmaL (u + w) = sigmaL u + sigmaL w := by
  simp only [sigmaL, lineSum_add, Pi.add_apply, Complex.ofReal_add, add_smul, smul_add]
  abel

theorem rhoL_smul (c : ℝ) (u : Fin 6 → ℝ) : rhoL (c • u) = c • rhoL u := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c (rhoL u)]
  simp only [rhoL, lineSum_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c (lineSum u)]
  module

theorem sigmaL_smul (c : ℝ) (u : Fin 6 → ℝ) : sigmaL (c • u) = c • sigmaL u := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c (sigmaL u)]
  simp only [sigmaL, lineSum_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c (lineSum u)]
  module

/-- The bilinear map `(u, v) ↦ ρ(u)σ(v)`. -/
noncomputable def evenBilin : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) →ₗ[ℝ] Matrix Four Four ℂ :=
  LinearMap.mk₂ ℝ (fun u v => rhoL u * sigmaL v)
    (fun u₁ u₂ v => by rw [rhoL_add, add_mul])
    (fun c u v => by rw [rhoL_smul, smul_mul_assoc])
    (fun u v₁ v₂ => by rw [sigmaL_add, mul_add])
    (fun c u v => by rw [sigmaL_smul, mul_smul_comm])

theorem evenBilin_apply (u v : Fin 6 → ℝ) : evenBilin u v = rhoL u * sigmaL v := rfl

theorem real_smul_one (r : ℝ) : (r • (1 : Matrix Four Four ℂ)) = ((r : ℂ)) • 1 :=
  RCLike.real_smul_eq_coe_smul (K := ℂ) r 1

/-- `(u, v) ↦ ρ(u)σ(v)` contracts as the even words do. -/
noncomputable def evenHom : CliffordAlgebra.EvenHom Q6 (Matrix Four Four ℂ) where
  bilin := evenBilin
  contract m := by
    rw [evenBilin_apply, rho_sigma, Algebra.algebraMap_eq_smul_one, real_smul_one]
  contract_mid m₁ m₂ m₃ := by
    rw [evenBilin_apply, evenBilin_apply, evenBilin_apply, mul_assoc, ← mul_assoc (sigmaL m₂),
      sigma_rho, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl

/-- **The even words of the six onto the operators of the four amplitudes.** -/
noncomputable def evenToFour : CliffordAlgebra.even Q6 →ₐ[ℝ] Matrix Four Four ℂ :=
  CliffordAlgebra.even.lift Q6 evenHom

theorem evenToFour_ι (u v : Fin 6 → ℝ) :
    evenToFour ((CliffordAlgebra.even.ι Q6).bilin u v) = rhoL u * sigmaL v :=
  CliffordAlgebra.even.lift_ι Q6 evenHom u v

theorem lineSum_singlet : lineSum (e6 0) = 0 := by
  simp [lineSum, e6, Pi.single_apply, Fin.succ_ne_zero]

theorem lineSum_line (s : Fin 5) : lineSum (e6 s.succ) = γ s := by
  simp [lineSum, e6, Pi.single_apply]

theorem e6_self (a : Fin 6) : e6 a a = 1 := by
  simp [e6]

theorem e6_line_singlet (s : Fin 5) : e6 s.succ 0 = 0 := by
  rw [e6, Pi.single_apply, ite_eq_right (Fin.succ_ne_zero s).symm]

theorem rhoL_singlet : rhoL (e6 0) = 1 := by
  rw [rhoL, lineSum_singlet, e6_self]
  simp

theorem sigmaL_singlet : sigmaL (e6 0) = 1 := by
  rw [sigmaL, lineSum_singlet, e6_self]
  simp

theorem rhoL_line (s : Fin 5) : rhoL (e6 s.succ) = I • γ s := by
  rw [rhoL, lineSum_line, e6_line_singlet]
  simp

theorem sigmaL_line (s : Fin 5) : sigmaL (e6 s.succ) = -(I • γ s) := by
  rw [sigmaL, lineSum_line, e6_line_singlet]
  simp

/-- The even word `J_n J_t` (`n` the singlet, `t` a line) in the even part. -/
noncomputable def singletLine (t : Fin 5) : CliffordAlgebra.even Q6 :=
  (CliffordAlgebra.even.ι Q6).bilin (e6 0) (e6 t.succ)

/-- The even word `J_s J_t` of two lines in the even part. -/
noncomputable def lineLine (s t : Fin 5) : CliffordAlgebra.even Q6 :=
  (CliffordAlgebra.even.ι Q6).bilin (e6 s.succ) (e6 t.succ)

theorem singletLine_val (t : Fin 5) : (singletLine t : CliffordAlgebra Q6) = cl 0 * cl t.succ := rfl

theorem lineLine_val (s t : Fin 5) : (lineLine s t : CliffordAlgebra Q6) = cl s.succ * cl t.succ :=
  rfl

/-- **`J_n J_t ↦ −iγ_t`.** -/
theorem evenToFour_singlet_line (t : Fin 5) : evenToFour (singletLine t) = (-I) • γ t := by
  rw [singletLine, evenToFour_ι, rhoL_singlet, sigmaL_line, Matrix.one_mul, neg_smul]

/-- **`J_s J_t ↦ γ_s γ_t`.** -/
theorem evenToFour_line_line (s t : Fin 5) : evenToFour (lineLine s t) = γ s * γ t := by
  rw [lineLine, evenToFour_ι, rhoL_line, sigmaL_line, mul_neg, smul_mul_smul_comm, I_mul_I,
    neg_one_smul, neg_neg]

/-- **A step of one system along a line is two vertical steps:** `γ_t = i · (J_n J_t ↦ ·)`. -/
theorem line_eq_i_singlet_line (t : Fin 5) : γ t = I • evenToFour (singletLine t) := by
  rw [evenToFour_singlet_line, smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]

/-- `i` is the image of the even word `(J_nJ_0)(J_nJ_1)(J_nJ_2)(J_nJ_3)(J_nJ_4)`, less its sign. -/
theorem evenToFour_five :
    evenToFour (singletLine 0 * singletLine 1 * singletLine 2 * singletLine 3 * singletLine 4) =
      (-I) • (1 : Matrix Four Four ℂ) := by
  simp only [map_mul, evenToFour_singlet_line, smul_mul_smul_comm]
  rw [γ_prod]
  congr 1
  linear_combination (-I * (I ^ 2 - 1)) * Complex.I_sq

/-! ## The map is onto -/

theorem mem_range_I_smul {X : Matrix Four Four ℂ} (hX : X ∈ evenToFour.range) :
    I • X ∈ evenToFour.range := by
  have hI : I • (1 : Matrix Four Four ℂ) ∈ evenToFour.range := by
    have h := evenToFour_five
    have hmem : (-I) • (1 : Matrix Four Four ℂ) ∈ evenToFour.range := ⟨_, h⟩
    have := Subalgebra.neg_mem _ hmem
    rwa [neg_smul, neg_neg] at this
  have := Subalgebra.mul_mem _ hI hX
  rwa [smul_mul_assoc, Matrix.one_mul] at this

theorem γ_mem_range (t : Fin 5) : γ t ∈ evenToFour.range := by
  rw [line_eq_i_singlet_line]
  exact mem_range_I_smul ⟨_, rfl⟩

theorem γγ_mem_range (s t : Fin 5) : γ s * γ t ∈ evenToFour.range :=
  ⟨_, evenToFour_line_line s t⟩

theorem obs_mem_range (k : Fin 16) : obs k ∈ evenToFour.range := by
  fin_cases k
  · exact Subalgebra.one_mem _
  · exact γ_mem_range 0
  · exact γ_mem_range 1
  · exact γ_mem_range 2
  · exact γ_mem_range 3
  · exact γ_mem_range 4
  · exact mem_range_I_smul (γγ_mem_range 0 1)
  · exact mem_range_I_smul (γγ_mem_range 0 2)
  · exact mem_range_I_smul (γγ_mem_range 0 3)
  · exact mem_range_I_smul (γγ_mem_range 0 4)
  · exact mem_range_I_smul (γγ_mem_range 1 2)
  · exact mem_range_I_smul (γγ_mem_range 1 3)
  · exact mem_range_I_smul (γγ_mem_range 1 4)
  · exact mem_range_I_smul (γγ_mem_range 2 3)
  · exact mem_range_I_smul (γγ_mem_range 2 4)
  · exact mem_range_I_smul (γγ_mem_range 3 4)

/-- A complex multiple is a real combination of the matrix and `i` times it. -/
theorem complex_smul_eq (z : ℂ) (X : Matrix Four Four ℂ) :
    z • X = z.re • X + z.im • (I • X) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul,
    ← add_smul]
  congr 1
  exact (Complex.re_add_im z).symm

/-- **Every operator of the four amplitudes is the image of an even word.** -/
theorem evenToFour_surjective : Function.Surjective evenToFour := by
  intro X
  have hX : X ∈ evenToFour.range := by
    rw [expand X]
    refine Subalgebra.sum_mem _ fun k _ => ?_
    rw [complex_smul_eq]
    exact Subalgebra.add_mem _ (Subalgebra.smul_mem _ (obs_mem_range k) _)
      (Subalgebra.smul_mem _ (mem_range_I_smul (obs_mem_range k)) _)
  obtain ⟨x, hx⟩ := hX
  exact ⟨x, hx⟩

/-! ## The map is one to one -/

theorem finrank_four : Module.finrank ℝ (Matrix Four Four ℂ) = 32 := by
  rw [Module.finrank_matrix, Complex.finrank_real_complex]
  simp

/-- The images of the 32 even words. -/
noncomputable def evenImage (S : EvenSets) : Matrix Four Four ℂ :=
  evenToFour ⟨clWord S.1, clWord_mem_even S⟩

theorem even_eq_sum (x : CliffordAlgebra.even Q6) :
    ∃ c : EvenSets → ℝ, x = ∑ S, c S • (⟨clWord S.1, clWord_mem_even S⟩ : CliffordAlgebra.even Q6) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (even_le_span x.1 x.2)
  refine ⟨c, Subtype.ext ?_⟩
  rw [← hc]
  simp

/-- **The 32 even words go to 32 independent operators.** -/
theorem evenImage_linearIndependent : LinearIndependent ℝ evenImage := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by rw [card_evenSets, finrank_four])
  intro X _
  obtain ⟨x, rfl⟩ := evenToFour_surjective X
  obtain ⟨c, rfl⟩ := even_eq_sum x
  rw [map_sum]
  refine Submodule.sum_mem _ fun S _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)

/-- **The map from the even words is one to one.** -/
theorem evenToFour_injective : Function.Injective evenToFour := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := even_eq_sum x
  rw [map_sum] at hx
  simp only [map_smul] at hx
  have hc := (Fintype.linearIndependent_iff.mp evenImage_linearIndependent) c hx
  simp [hc]

theorem evenToFour_bijective : Function.Bijective evenToFour :=
  ⟨evenToFour_injective, evenToFour_surjective⟩

/-- **Proposition 37: the even Clifford algebra of the six is, as a real algebra, all the operators
of the four amplitudes**, with `J_nJ_t ↦ −iγ_t` and `J_sJ_t ↦ γ_sγ_t`. -/
noncomputable def evenEquivFour : CliffordAlgebra.even Q6 ≃ₐ[ℝ] Matrix Four Four ℂ :=
  AlgEquiv.ofBijective evenToFour evenToFour_bijective

theorem evenEquivFour_apply (x : CliffordAlgebra.even Q6) : evenEquivFour x = evenToFour x := rfl

end Four

/-! ## The vertical step on the sixty-four sets is the Clifford algebra, faithfully -/

section Step

/-- `v ↦ J(v)` as a linear map. -/
noncomputable def JvLin : (Fin 6 → ℝ) →ₗ[ℝ] Module.End ℝ (Finset (Fin 6) → ℝ) where
  toFun v := Jv v
  map_add' v w := by simp only [Jv, εv_add, ιv_add]; abel
  map_smul' c v := by simp only [Jv, εv_smul, ιv_smul, smul_add, RingHom.id_apply]

/-- **`ι(v) ↦ J(v)`** lifts to the Clifford algebra: the vertical steps are its representation. -/
noncomputable def stepRep : CliffordAlgebra Q6 →ₐ[ℝ] Module.End ℝ (Finset (Fin 6) → ℝ) :=
  CliffordAlgebra.lift Q6 ⟨JvLin, fun m => by
    change Jv m * Jv m = _
    rw [Jv_mul_self, Algebra.algebraMap_eq_smul_one, Q6_apply, dotProduct]⟩

theorem stepRep_cl (a : Fin 6) : stepRep (cl a) = Jx a := by
  rw [stepRep, cl, CliffordAlgebra.lift_ι_apply]
  change Jv (e6 a) = Jx a
  rw [Jv, e6, εv_single, ιv_single]
  rfl

theorem stepRep_clWord (S : Finset (Fin 6)) : stepRep (clWord S) = ordProd Jx S := by
  rw [clWord, ordProd, ordProd, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  exact stepRep_cl a

/-- The span of all the words. -/
noncomputable def Pall : Submodule ℝ (CliffordAlgebra Q6) :=
  Submodule.span ℝ (Set.range clWord)

theorem cl_mul_mem_all (a : Fin 6) {x : CliffordAlgebra Q6} (hx : x ∈ Pall) : cl a * x ∈ Pall := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨S, rfl⟩ := hy
    rw [cl_mul_clWord, neg_one_pow_mul_eq_smul]
    refine Submodule.smul_mem _ _ ?_
    split_ifs
    · exact Submodule.subset_span ⟨_, rfl⟩
    · exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

/-- The Clifford algebra of the six is spanned by its 64 ordered words. -/
theorem all_le_span (x : CliffordAlgebra Q6) : x ∈ Pall := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨∅, ?_⟩)
    simp [clWord]
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | ι_mul x m hx =>
    rw [ι_eq_sum_cl, Finset.sum_mul]
    exact Submodule.sum_mem _ fun a _ => by
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ _ (cl_mul_mem_all a hx)

/-- **The vertical steps represent the Clifford algebra of the six faithfully.** -/
theorem stepRep_injective : Function.Injective stepRep := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (all_le_span x)
  rw [← hc] at hx ⊢
  have h0 := congrArg (fun f => f (Pi.single ∅ 1)) hx
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, stepRep_clWord,
    ordProd_Jx_vac, LinearMap.zero_apply] at h0
  have hcS : ∀ S, c S = 0 := by
    intro S
    have := congrFun h0 S
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Pi.zero_apply] at this
    exact this
  simp [hcS]

end Step

end Comparison.SysExt

end
