import Comparison.System.Geometry.Divisions

/-!
# The geometry of comparison: Definition 15's real form of a division, in a basis

For every set `S` of directions of P1's real six
(a division in a basis), the generators of Definition 15's real form (`realFormAlg`: trace zero, and
`X ⊗ 1 + 1 ⊗ X` keeps `q_S(P1's real six)`) are exactly the real combinations of the fifteen
generators of the real form, the kept rotations and `i` times the moved ones (`realFormAlg_ofSet`); they
form a real space of dimension 15 (`finrank_realFormSpan`). For the division of the lines `D` with the
singlet undivided this is the Lie algebra of the Lemma: `{X : tr X = 0, X†h_D + h_DX = 0}` for `|D|`
even and `{X : tr X = 0, XC_D = C_DX}` for `|D|` odd (`realFormAlg_lines_even`,
`realFormAlg_lines_odd`).

The proof: each generator turns exactly one plane of the six (`gen_acts_matrix`); the square root of the sign `q_S` is `i`
on `S` and `1` off it, so a kept rotation and `i` times a moved rotation keep `q_S(ℝ⁶)` (`inHalf_realGen6`).
Conversely an `X` of trace zero is `Z + iY` with `Z`, `Y` real combinations of the fifteen; `Z` keeps
`q_S(ℝ⁶)`, so `iY` does as well as `Y`, and `q_S(ℝ⁶) ∩ i q_S(ℝ⁶) = 0` gives `Y = 0` on the six, hence
every coefficient of `Y` is zero (`comb_eq_zero`).
-/

open Matrix Complex Module

namespace Comparison.System

namespace Geometry

/-! ## The half of a coordinate division -/

/-- The diagonal projector of the coordinate division `S`. -/
noncomputable def projOf (S : Finset (Fin 6)) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.diagonal fun a => if a ∈ S then (1 : ℝ) else 0

/-- The half of the coordinate division `S` on one coordinate: `i` on `S`, `1` off `S`. -/
noncomputable def qS (S : Finset (Fin 6)) (a : Fin 6) : ℂ := if a ∈ S then Complex.I else 1

theorem qS_ne_zero (S : Finset (Fin 6)) (a : Fin 6) : qS S a ≠ 0 := by
  unfold qS; split_ifs <;> simp

theorem halfOf_projOf_mulVec (S : Finset (Fin 6)) (z : Fin 6 → ℂ) :
    halfOf (projOf S) *ᵥ z = fun a => qS S a * z a := by
  have hm : (projOf S).map ((↑) : ℝ → ℂ) =
      Matrix.diagonal fun a => if a ∈ S then (1 : ℂ) else 0 := by
    ext i j
    simp only [projOf, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  funext a
  rw [halfOf, hm, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul, qS]
  split_ifs <;> ring

/-- `w` lies in the square root of the sign of the coordinate division: imaginary on `S`, real off `S`. -/
def InHalf (S : Finset (Fin 6)) (w : Fin 6 → ℂ) : Prop :=
  ∀ a, (a ∈ S → (w a).re = 0) ∧ (a ∉ S → (w a).im = 0)

theorem mem_halfSix_iff (S : Finset (Fin 6)) (A : Matrix Four Four ℂ) :
    A ∈ halfSix (projOf S) ↔ ∃ w, A = GroupsContinuumLaw.ιC w ∧ InHalf S w := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨_, rfl, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
    · rw [halfOf_projOf_mulVec]; simp [qS, ha]
    · rw [halfOf_projOf_mulVec]; simp [qS, ha]
  · rintro ⟨w, rfl, hw⟩
    refine ⟨fun a => if a ∈ S then (w a).im else (w a).re, ?_⟩
    rw [halfOf_projOf_mulVec]
    congr 1
    funext a
    simp only [qS]
    by_cases ha : a ∈ S
    · simp only [ha, if_true]
      apply Complex.ext <;> simp [(hw a).1 ha]
    · simp only [ha, if_false, one_mul]
      apply Complex.ext <;> simp [(hw a).2 ha]

theorem InHalf.add {S : Finset (Fin 6)} {w w' : Fin 6 → ℂ} (h : InHalf S w) (h' : InHalf S w') :
    InHalf S (w + w') := fun a =>
  ⟨fun ha => by simp [(h a).1 ha, (h' a).1 ha], fun ha => by simp [(h a).2 ha, (h' a).2 ha]⟩

theorem InHalf.neg {S : Finset (Fin 6)} {w : Fin 6 → ℂ} (h : InHalf S w) : InHalf S (-w) := fun a =>
  ⟨fun ha => by simp [(h a).1 ha], fun ha => by simp [(h a).2 ha]⟩

theorem InHalf.smul_real {S : Finset (Fin 6)} {w : Fin 6 → ℂ} (r : ℝ) (h : InHalf S w) :
    InHalf S ((r : ℂ) • w) := fun a =>
  ⟨fun ha => by simp [(h a).1 ha], fun ha => by simp [(h a).2 ha]⟩

theorem InHalf.eq_zero {S : Finset (Fin 6)} {w : Fin 6 → ℂ} (h : InHalf S w)
    (hI : InHalf S (Complex.I • w)) : w = 0 := by
  funext a
  by_cases ha : a ∈ S
  · have h1 := (h a).1 ha
    have h2 := (hI a).1 ha
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub, neg_eq_zero] at h2
    exact Complex.ext h1 h2
  · have h1 := (h a).2 ha
    have h2 := (hI a).2 ha
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_add] at h2
    exact Complex.ext h2 h1

theorem ιC_smul (c : ℂ) (w : Fin 6 → ℂ) : GroupsContinuumLaw.ιC (c • w) = c • GroupsContinuumLaw.ιC w := by
  simp only [GroupsContinuumLaw.ιC, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul]

theorem ιC_neg (w : Fin 6 → ℂ) : GroupsContinuumLaw.ιC (-w) = -GroupsContinuumLaw.ιC w := by
  simp only [GroupsContinuumLaw.ιC, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

theorem ιC_zero : GroupsContinuumLaw.ιC 0 = 0 := by
  simp [GroupsContinuumLaw.ιC]

theorem halfSix_zero (S : Finset (Fin 6)) : (0 : Matrix Four Four ℂ) ∈ halfSix (projOf S) :=
  (mem_halfSix_iff S 0).mpr ⟨0, ιC_zero.symm, fun a => ⟨fun _ => by simp, fun _ => by simp⟩⟩

theorem halfSix_add {S : Finset (Fin 6)} {A B : Matrix Four Four ℂ} (hA : A ∈ halfSix (projOf S))
    (hB : B ∈ halfSix (projOf S)) : A + B ∈ halfSix (projOf S) := by
  obtain ⟨w, rfl, hw⟩ := (mem_halfSix_iff S A).mp hA
  obtain ⟨w', rfl, hw'⟩ := (mem_halfSix_iff S B).mp hB
  exact (mem_halfSix_iff S _).mpr ⟨w + w', (GroupsContinuumLaw.ιC_add w w').symm, hw.add hw'⟩

theorem halfSix_neg {S : Finset (Fin 6)} {A : Matrix Four Four ℂ} (hA : A ∈ halfSix (projOf S)) :
    -A ∈ halfSix (projOf S) := by
  obtain ⟨w, rfl, hw⟩ := (mem_halfSix_iff S A).mp hA
  exact (mem_halfSix_iff S _).mpr ⟨-w, (ιC_neg w).symm, hw.neg⟩

theorem halfSix_sub {S : Finset (Fin 6)} {A B : Matrix Four Four ℂ} (hA : A ∈ halfSix (projOf S))
    (hB : B ∈ halfSix (projOf S)) : A - B ∈ halfSix (projOf S) := by
  rw [sub_eq_add_neg]; exact halfSix_add hA (halfSix_neg hB)

theorem halfSix_smul {S : Finset (Fin 6)} {A : Matrix Four Four ℂ} (r : ℝ)
    (hA : A ∈ halfSix (projOf S)) : (r : ℂ) • A ∈ halfSix (projOf S) := by
  obtain ⟨w, rfl, hw⟩ := (mem_halfSix_iff S A).mp hA
  exact (mem_halfSix_iff S _).mpr ⟨(r : ℂ) • w, (ιC_smul _ w).symm, hw.smul_real r⟩

/-- `q_S(ℝ⁶) ∩ i q_S(ℝ⁶) = 0`. -/
theorem halfSix_inter_I {S : Finset (Fin 6)} {A : Matrix Four Four ℂ} (hA : A ∈ halfSix (projOf S))
    (hIA : Complex.I • A ∈ halfSix (projOf S)) : A = 0 := by
  obtain ⟨w, rfl, hw⟩ := (mem_halfSix_iff S A).mp hA
  obtain ⟨w', hw'e, hw'⟩ := (mem_halfSix_iff S _).mp hIA
  rw [← ιC_smul] at hw'e
  have he : Complex.I • w = w' := GroupsContinuumLaw.ιC_injective hw'e
  rw [← he] at hw'
  rw [hw.eq_zero hw', ιC_zero]

/-! ## The action of the generators on the six -/

theorem act_add_left (X Y A : Matrix Four Four ℂ) : act (X + Y) A = act X A + act Y A := by
  simp only [act, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]; abel

theorem act_smul_left (c : ℂ) (X A : Matrix Four Four ℂ) : act (c • X) A = c • act X A := by
  simp only [act, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add]

theorem act_smul_right (c : ℂ) (X A : Matrix Four Four ℂ) : act X (c • A) = c • act X A := by
  simp only [act, Matrix.smul_mul, Matrix.mul_smul, smul_add]

theorem act_zero_left (A : Matrix Four Four ℂ) : act 0 A = 0 := by
  simp [act]

theorem act_sum_left (f : Fin 5 ⊕ Fin 10 → Matrix Four Four ℂ) (A : Matrix Four Four ℂ) :
    act (∑ x, f x) A = ∑ x, act (f x) A := by
  simp only [act, Matrix.transpose_sum, Finset.sum_mul, Matrix.mul_sum, Finset.sum_add_distrib]

theorem act_ιC (X : Matrix Four Four ℂ) (w : Fin 6 → ℂ) :
    act X (GroupsContinuumLaw.ιC w) = ∑ c, w c • act X (sixP1 c) := by
  simp only [act, GroupsContinuumLaw.ιC, Matrix.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← Finset.sum_add_distrib, smul_add]

/-- A generator acts on the six by the rotation of its plane, on coordinates. -/
theorem act_gen_ιC (x : Fin 5 ⊕ Fin 10) (w : Fin 6 → ℂ) :
    act (gen x) (GroupsContinuumLaw.ιC w) =
      GroupsContinuumLaw.ιC (fun d => ∑ c, ((rotMat (plane x) d c : ℤ) : ℂ) * w c) := by
  rw [act_ιC]
  simp only [gen_acts_matrix, Finset.smul_sum, smul_smul, GroupsContinuumLaw.ιC, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]

/-- The rotation of the plane `p` on coordinates: `w_{p.1}` goes to `2w_{p.1}` at `p.2`, `w_{p.2}`
to `−2w_{p.2}` at `p.1`. -/
theorem rotMat_sum (p : Fin 6 × Fin 6) (hp : p.1 ≠ p.2) (w : Fin 6 → ℂ) (d : Fin 6) :
    ∑ c, ((rotMat p d c : ℤ) : ℂ) * w c =
      if d = p.2 then 2 * w p.1 else if d = p.1 then -2 * w p.2 else 0 := by
  simp only [rotMat, Matrix.of_apply]
  by_cases h2 : d = p.2
  · subst h2
    have hne : ¬(p.2 = p.1) := fun e => hp e.symm
    simp [hne]
  · by_cases h1 : d = p.1
    · subst h1
      simp [h2]
    · simp [h1, h2]

/-! ## The generators of the real form of a coordinate division -/

/-- The factor of a generator of the real form of the coordinate division `S`: `1` when kept, `i`
when moved. -/
noncomputable def realFactor6 (S : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) : ℂ :=
  if Kept S x then 1 else Complex.I

/-- **The fifteen generators of the real form of the coordinate division `S`:** the kept rotations, and `i`
times the moved rotations. -/
noncomputable def realGen6 (S : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) : Matrix Four Four ℂ :=
  realFactor6 S x • gen x

theorem realFactor6_ne_zero (S : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) : realFactor6 S x ≠ 0 := by
  unfold realFactor6; split_ifs <;> simp

theorem realGen_eq_realGen6 (D : Finset (Fin 5)) : realGen D = realGen6 (linesDiv D) := by
  funext x
  rw [realGen_eq, realGen6]
  congr 1

/-- A kept rotation, and `i` times a moved rotation, keep `q_S(ℝ⁶)`. -/
theorem inHalf_realGen6 (S : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) (w : Fin 6 → ℂ)
    (hw : InHalf S w) :
    InHalf S (realFactor6 S x • fun d => ∑ c, ((rotMat (plane x) d c : ℤ) : ℂ) * w c) := by
  have hp := ne_of_lt (plane_lt x)
  have hk := kept_iff S x
  obtain ⟨h1a, h1b⟩ := hw (plane x).1
  obtain ⟨h2a, h2b⟩ := hw (plane x).2
  intro d
  simp only [Pi.smul_apply, smul_eq_mul, rotMat_sum _ hp]
  by_cases hd2 : d = (plane x).2
  · subst hd2
    rw [if_pos rfl]
    by_cases s1 : (plane x).1 ∈ S <;> by_cases s2 : (plane x).2 ∈ S
    · have hK : Kept S x := hk.mpr (iff_of_true s1 s2)
      simp [realFactor6, hK, h1a s1, s2]
    · have hK : ¬Kept S x := fun h => s2 ((hk.mp h).mp s1)
      simp [realFactor6, hK, h1a s1, s2]
    · have hK : ¬Kept S x := fun h => s1 ((hk.mp h).mpr s2)
      simp [realFactor6, hK, h1b s1, s2]
    · have hK : Kept S x := hk.mpr (iff_of_false s1 s2)
      simp [realFactor6, hK, h1b s1, s2]
  · by_cases hd1 : d = (plane x).1
    · subst hd1
      rw [if_neg hd2, if_pos rfl]
      by_cases s1 : (plane x).1 ∈ S <;> by_cases s2 : (plane x).2 ∈ S
      · have hK : Kept S x := hk.mpr (iff_of_true s1 s2)
        simp [realFactor6, hK, h2a s2, s1]
      · have hK : ¬Kept S x := fun h => s2 ((hk.mp h).mp s1)
        simp [realFactor6, hK, h2b s2, s1]
      · have hK : ¬Kept S x := fun h => s1 ((hk.mp h).mpr s2)
        simp [realFactor6, hK, h2a s2, s1]
      · have hK : Kept S x := hk.mpr (iff_of_false s1 s2)
        simp [realFactor6, hK, h2b s2, s1]
    · simp [hd1, hd2]

theorem realGen6_trace (S : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) : (realGen6 S x).trace = 0 := by
  rw [realGen6, Matrix.trace_smul, gen_trace', smul_zero]

/-- Each of the fifteen is a generator of Definition 15's real form. -/
theorem realGen6_mem (S : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) :
    realGen6 S x ∈ realFormAlg (projOf S) := by
  refine ⟨realGen6_trace S x, fun A hA => ?_⟩
  obtain ⟨w, rfl, hw⟩ := (mem_halfSix_iff S A).mp hA
  refine (mem_halfSix_iff S _).mpr ⟨_, ?_, inHalf_realGen6 S x w hw⟩
  rw [realGen6, act_smul_left, act_gen_ιC, ιC_smul]

theorem span_mem_realFormAlg (S : Finset (Fin 6)) :
    ∀ X ∈ Submodule.span ℝ (Set.range (realGen6 S)), X ∈ realFormAlg (projOf S) := by
  intro X hX
  induction hX using Submodule.span_induction with
  | mem X h =>
    obtain ⟨x, rfl⟩ := h
    exact realGen6_mem S x
  | zero => exact ⟨Matrix.trace_zero _ _, fun A _ => by rw [act_zero_left]; exact halfSix_zero S⟩
  | add X Y _ _ hX hY =>
    exact ⟨by rw [Matrix.trace_add, hX.1, hY.1, add_zero],
      fun A hA => by rw [act_add_left]; exact halfSix_add (hX.2 A hA) (hY.2 A hA)⟩
  | smul r X _ hX =>
    refine ⟨by rw [Matrix.trace_smul, hX.1, smul_zero], fun A hA => ?_⟩
    rw [← Complex.coe_smul, act_smul_left]
    exact halfSix_smul r (hX.2 A hA)

theorem span_subset_realFormAlg (S : Finset (Fin 6)) :
    (Submodule.span ℝ (Set.range (realGen6 S)) : Set (Matrix Four Four ℂ)) ⊆
      realFormAlg (projOf S) :=
  fun X hX => span_mem_realFormAlg S X hX

/-! ## The converse: every generator of Definition 15's real form is a real combination -/

theorem realGen6_real_comb (S : Finset (Fin 6)) (X : Matrix Four Four ℂ) (htr : X.trace = 0) :
    ∃ p q : Fin 5 ⊕ Fin 10 → ℝ, X = ∑ x, (p x : ℂ) • realGen6 S x +
      Complex.I • ∑ x, (q x : ℂ) • realGen6 S x := by
  obtain ⟨c, hc⟩ := exists_gen_coeffs X htr
  set w : Fin 5 ⊕ Fin 10 → ℂ := fun x => c x / realFactor6 S x with hw
  refine ⟨fun x => (w x).re, fun x => (w x).im, ?_⟩
  rw [hc, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul, ← add_smul, realGen6, smul_smul]
  congr 1
  have hre : ((w x).re : ℂ) + Complex.I * ((w x).im : ℂ) = w x := by
    rw [mul_comm]; exact Complex.re_add_im (w x)
  rw [hre, hw]
  field_simp [realFactor6_ne_zero S x]

theorem act_comb_sixP1 (S : Finset (Fin 6)) (q : Fin 5 ⊕ Fin 10 → ℝ) (c : Fin 6) :
    act (∑ x, (q x : ℂ) • realGen6 S x) (sixP1 c) =
      GroupsContinuumLaw.ιC (fun d => ∑ x, (q x : ℂ) * realFactor6 S x * ((rotMat (plane x) d c : ℤ) : ℂ)) := by
  rw [act_sum_left]
  simp only [act_smul_left, realGen6, gen_acts_matrix, Finset.smul_sum, smul_smul, GroupsContinuumLaw.ιC,
    Finset.sum_smul, mul_assoc]
  rw [Finset.sum_comm]

/-- A real combination of the fifteen that rotations no direction of the six is zero. -/
theorem comb_eq_zero (S : Finset (Fin 6)) (q : Fin 5 ⊕ Fin 10 → ℝ)
    (h : ∀ c, act (∑ x, (q x : ℂ) • realGen6 S x) (sixP1 c) = 0) : ∀ x, q x = 0 := by
  intro y
  have hc := h (plane y).1
  rw [act_comb_sixP1] at hc
  have hd := congrArg (GroupsContinuumLaw.ip (sixP1 (plane y).2)) hc
  rw [GroupsContinuumLaw.ip_ιC] at hd
  have hip0 : GroupsContinuumLaw.ip (sixP1 (plane y).2) 0 = 0 := by simp [GroupsContinuumLaw.ip]
  rw [hip0, Finset.sum_eq_single y] at hd
  · have hy : rotMat (plane y) (plane y).2 (plane y).1 = 2 := by
      simp [rotMat]
    rw [hy] at hd
    have hne := realFactor6_ne_zero S y
    have h2 : (q y : ℂ) = 0 := by
      rcases mul_eq_zero.mp hd with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact h''
        · exact absurd h'' hne
      · norm_num at h'
    exact_mod_cast h2
  · intro x _ hxy
    have hne : ¬((plane y).2 = (plane x).2 ∧ (plane y).1 = (plane x).1) := by
      rintro ⟨e2, e1⟩
      exact hxy (plane_bijective.1 (Prod.ext e1.symm e2.symm))
    have hne' : ¬((plane y).2 = (plane x).1 ∧ (plane y).1 = (plane x).2) := by
      rintro ⟨e2, e1⟩
      have h3 := plane_lt x
      have h4 := plane_lt y
      rw [← e2, ← e1] at h3
      exact absurd (h3.trans h4) (lt_irrefl _)
    simp only [rotMat, Matrix.of_apply, if_neg hne, if_neg hne', Int.cast_zero, mul_zero]
  · intro hy; exact absurd (Finset.mem_univ y) hy

theorem realFormAlg_subset_span (S : Finset (Fin 6)) :
    realFormAlg (projOf S) ⊆
      (Submodule.span ℝ (Set.range (realGen6 S)) : Set (Matrix Four Four ℂ)) := by
  rintro X ⟨htr, hkeep⟩
  obtain ⟨p, q, hX⟩ := realGen6_real_comb S X htr
  have hmem : ∀ r : Fin 5 ⊕ Fin 10 → ℝ,
      ∑ x, (r x : ℂ) • realGen6 S x ∈ Submodule.span ℝ (Set.range (realGen6 S)) := by
    intro r
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [Complex.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hZ := span_mem_realFormAlg S _ (hmem p)
  have hY := span_mem_realFormAlg S _ (hmem q)
  have hY0 : ∀ c, act (∑ x, (q x : ℂ) • realGen6 S x) (sixP1 c) = 0 := by
    intro c
    have hA : qS S c • sixP1 c ∈ halfSix (projOf S) := by
      refine (mem_halfSix_iff S _).mpr ⟨Pi.single c (qS S c), ?_, fun a => ?_⟩
      · rw [GroupsContinuumLaw.sixP1_eq_ιC, ← ιC_smul]
        congr 1
        funext a
        simp [Pi.single_apply]
      · by_cases hac : a = c
        · subst hac
          constructor
          · intro ha; simp [qS, ha]
          · intro ha; simp [qS, ha]
        · simp [hac]
    have h1 := hkeep _ hA
    have h2 := hZ.2 _ hA
    have h3 := hY.2 _ hA
    have hXZ : act X (qS S c • sixP1 c) - act (∑ x, (p x : ℂ) • realGen6 S x) (qS S c • sixP1 c) =
        Complex.I • act (∑ x, (q x : ℂ) • realGen6 S x) (qS S c • sixP1 c) := by
      rw [hX, act_add_left, act_smul_left]; abel
    have h4 := halfSix_sub h1 h2
    rw [hXZ] at h4
    have h5 := halfSix_inter_I h3 h4
    rw [act_smul_right] at h5
    exact (smul_eq_zero.mp h5).resolve_left (qS_ne_zero S c)
  have hq := comb_eq_zero S q hY0
  have hY' : ∑ x, (q x : ℂ) • realGen6 S x = 0 := by
    simp [hq]
  rw [hX, hY', smul_zero, add_zero]
  exact hmem p

/-- **Definition 15's real form in a basis:** for every set `S` of directions of P1's real six, the
generators of the real form of the division `S` (trace zero, `X ⊗ 1 + 1 ⊗ X` keeps `q_S(ℝ⁶)`) are
exactly the real combinations of the kept rotations and `i` times the moved rotations. -/
theorem realFormAlg_ofSet (S : Finset (Fin 6)) :
    realFormAlg (projOf S) = (Submodule.span ℝ (Set.range (realGen6 S)) : Set (Matrix Four Four ℂ)) :=
  Set.Subset.antisymm (realFormAlg_subset_span S) (span_subset_realFormAlg S)

theorem realGen6_linearIndependent (S : Finset (Fin 6)) : LinearIndependent ℂ (realGen6 S) := by
  have hu := gen_linearIndependent_complex.units_smul
    (fun x => Units.mk0 (realFactor6 S x) (realFactor6_ne_zero S x))
  convert hu using 1
  funext x
  simp [realGen6, Units.smul_def]

/-- The real form of every coordinate division has real dimension 15. -/
theorem finrank_realFormSpan (S : Finset (Fin 6)) :
    finrank ℝ (Submodule.span ℝ (Set.range (realGen6 S))) = 15 := by
  have hR : LinearIndependent ℝ (realGen6 S) :=
    (realGen6_linearIndependent S).restrict_scalars' ℝ
  rw [finrank_span_eq_card hR]
  simp

/-- Calling the other part divided gives the same real form: `realFormAlg (P_{Sᶜ}) = realFormAlg (P_S)`. -/
theorem realFormAlg_compl (S : Finset (Fin 6)) :
    realFormAlg (projOf Sᶜ) = realFormAlg (projOf S) := by
  have h : realGen6 Sᶜ = realGen6 S := by
    funext x
    have hk := kept_compl S x
    by_cases hx : Kept S x
    · simp [realGen6, realFactor6, hx, hk.mpr hx]
    · have hx' : ¬Kept Sᶜ x := fun h' => hx (hk.mp h')
      simp [realGen6, realFactor6, hx, hx']
  rw [realFormAlg_ofSet, realFormAlg_ofSet, h]

/-- **The real form of the division of the lines `D` is the real span of the Lemma's fifteen.** -/
theorem realFormAlg_lines (D : Finset (Fin 5)) :
    realFormAlg (projOf (linesDiv D)) =
      (Submodule.span ℝ (Set.range (realGen D)) : Set (Matrix Four Four ℂ)) := by
  rw [realGen_eq_realGen6]
  exact realFormAlg_ofSet _

/-- **Even divisions of the lines:** Definition 15's real form is `{X : tr X = 0, X†h_D + h_DX = 0}`. -/
theorem realFormAlg_lines_even (D : Finset (Fin 5)) (hD : D.card % 2 = 0) (X : Matrix Four Four ℂ) :
    X ∈ realFormAlg (projOf (linesDiv D)) ↔
      X.trace = 0 ∧ Xᴴ * hermForm D + hermForm D * X = 0 := by
  rw [realFormAlg_lines]
  exact (realGen_span_iff_even D hD X).symm

/-- **Odd divisions of the lines:** Definition 15's real form is `{X : tr X = 0, XC_D = C_DX}`, with
`C_Dv = γ_DJv̄`. -/
theorem realFormAlg_lines_odd (D : Finset (Fin 5)) (hD : D.card % 2 = 1) (X : Matrix Four Four ℂ) :
    X ∈ realFormAlg (projOf (linesDiv D)) ↔
      X.trace = 0 ∧ X * (gammaD D * J) = (gammaD D * J) * X.map star := by
  rw [realFormAlg_lines]
  exact (realGen_span_iff_odd D hD X).symm

/-! ## Definition 15: every generator is one kept plus one moved -/

/-- **Every generator is one kept plus one moved.** For every projector `P` (`P² = P`) and every
`X`, with `θ = 1 − 2P`: `X = ½(X + θXθ) + ½(X − θXθ)`, the first part kept (it commutes with `θ`) and
the second moved (it anticommutes with `θ`); for a symmetric `P` both parts of an antisymmetric `X`
are antisymmetric. -/
theorem kept_add_moved (P : Matrix (Fin 6) (Fin 6) ℝ) (hP : P * P = P)
    (X : Matrix (Fin 6) (Fin 6) ℝ) :
    X = (1 / 2 : ℝ) • (X + signOf P * X * signOf P) + (1 / 2 : ℝ) • (X - signOf P * X * signOf P) ∧
    KeptBy P ((1 / 2 : ℝ) • (X + signOf P * X * signOf P)) ∧
    MovedBy P ((1 / 2 : ℝ) • (X - signOf P * X * signOf P)) ∧
    (Pᵀ = P → Xᵀ = -X →
      ((1 / 2 : ℝ) • (X + signOf P * X * signOf P))ᵀ =
        -((1 / 2 : ℝ) • (X + signOf P * X * signOf P)) ∧
      ((1 / 2 : ℝ) • (X - signOf P * X * signOf P))ᵀ =
        -((1 / 2 : ℝ) • (X - signOf P * X * signOf P))) := by
  set θ := signOf P with hθdef
  have hθ : θ * θ = 1 := by
    rw [hθdef, signOf]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hP, smul_smul]
    module
  have hθ2 : ∀ M : Matrix (Fin 6) (Fin 6) ℝ, θ * (θ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hθ, Matrix.one_mul]
  refine ⟨by module, ?_, ?_, fun hPs hX => ?_⟩
  · show _ * θ = θ * _
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
      hθ, hθ2, Matrix.mul_one]
    module
  · show _ * θ = -(θ * _)
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
      hθ, hθ2, Matrix.mul_one]
    module
  · have hθT : θᵀ = θ := by
      rw [hθdef, signOf, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hPs]
    constructor
    · simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul, hθT, hX,
        Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      module
    · simp only [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_mul, hθT, hX,
        Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      module

end Geometry

open Comparison.System.Geometry

/-- **Proposition 21, the real form of a division in a basis (Definition 15, the Lemma and its
converse).** For every set `S` of directions of P1's real six, the generators of Definition 15's real
form (trace zero, `X ⊗ 1 + 1 ⊗ X` keeps `q_S(P1's real six)`) are exactly the real combinations of
the fifteen generators of the real form, the kept rotations and `i` times the moved ones, which are
independent; calling the other part divided gives the same real form; for the division of the lines
`D` with the singlet undivided it is `{X : tr X = 0, X†h_D + h_DX = 0}` (`|D|` even) or
`{X : tr X = 0, XC_D = C_DX}` (`|D|` odd); every generator of the six is one kept plus one moved.
Recognition: `su(4)`, `sl(2,ℍ)`, `su(2,2)`, `sl(4,ℝ)`, the real forms of the twistor group. -/
theorem Geometry.realForm_statement :
    (∀ S : Finset (Fin 6), realFormAlg (projOf S) =
      (Submodule.span ℝ (Set.range (realGen6 S)) : Set (Matrix Four Four ℂ))) ∧
    (∀ S : Finset (Fin 6), LinearIndependent ℂ (realGen6 S) ∧
      finrank ℝ (Submodule.span ℝ (Set.range (realGen6 S))) = 15) ∧
    (∀ S : Finset (Fin 6), realFormAlg (projOf Sᶜ) = realFormAlg (projOf S)) ∧
    (∀ D : Finset (Fin 5), D.card % 2 = 0 → ∀ X : Matrix Four Four ℂ,
      X ∈ realFormAlg (projOf (linesDiv D)) ↔
        X.trace = 0 ∧ Xᴴ * hermForm D + hermForm D * X = 0) ∧
    (∀ D : Finset (Fin 5), D.card % 2 = 1 → ∀ X : Matrix Four Four ℂ,
      X ∈ realFormAlg (projOf (linesDiv D)) ↔
        X.trace = 0 ∧ X * (gammaD D * J) = (gammaD D * J) * X.map star) ∧
    (∀ P : Matrix (Fin 6) (Fin 6) ℝ, P * P = P → ∀ X : Matrix (Fin 6) (Fin 6) ℝ,
      X = (1 / 2 : ℝ) • (X + signOf P * X * signOf P) + (1 / 2 : ℝ) • (X - signOf P * X * signOf P) ∧
      KeptBy P ((1 / 2 : ℝ) • (X + signOf P * X * signOf P)) ∧
      MovedBy P ((1 / 2 : ℝ) • (X - signOf P * X * signOf P))) :=
  ⟨realFormAlg_ofSet, fun S => ⟨realGen6_linearIndependent S, finrank_realFormSpan S⟩,
    realFormAlg_compl, realFormAlg_lines_even, realFormAlg_lines_odd,
    fun P hP X => ⟨(kept_add_moved P hP X).1, (kept_add_moved P hP X).2.1,
      (kept_add_moved P hP X).2.2.1⟩⟩

end Comparison.System
