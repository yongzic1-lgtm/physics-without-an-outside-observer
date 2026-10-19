import Comparison.System.Geometry.TwoThings
import Comparison.Article.Commutant2

/-!
# The geometry of comparison, Book II continued: the operators the ten rotations keep (Prop. 15, part 1)

The operators on `N` systems,
`Op N = Matrix (Fin N → Four) (Fin N → Four) ℂ`, and the tools of Proposition 15 for every `N`:

* `kronN A = A₁ ⊗ ⋯ ⊗ A_N`, `tpow N U = U^{⊗N}`; `kronN_mul`, `trace_kronN`, `kronN_conjTranspose`;
* the strings `pstr σ = X_{σ₁} ⊗ ⋯ ⊗ X_{σ_N}` of the sixteen observables: orthogonal,
  `Tr(P_σ P_τ) = 4^N δ_στ` (`trace_pstr_mul`), a basis (`expand_pstr`: `X = Σ_σ c_σ(X) P_σ`);
* `coef_of_commute`: if `X` commutes with `U^{⊗N}` and `U†X_kU = s_k X_{π k}` on the sixteen, then
  `c_σ(X) = (∏ s_{σ_i}) c_{π∘σ}(X)`;
* the swaps `permOp π`, the pairings `Eab a b` (`E` on the systems `a`, `b`), the algebra they generate
  `brauerAlg N`, and `brauer_kept`: **for every `N`, every product of swaps and `E`'s is kept by every
  rotation of `Sp(2)`** (the easy half of Proposition 15).
-/

open scoped Kronecker
open Matrix Complex Module

namespace Comparison.System

namespace Geometry

/-- The operators on `N` systems. -/
abbrev Op (N : ℕ) := Matrix (Fin N → Four) (Fin N → Four) ℂ

/-- The tensor product `A₁ ⊗ ⋯ ⊗ A_N`. -/
def kronN {N : ℕ} (A : Fin N → Matrix Four Four ℂ) : Op N :=
  Matrix.of fun w v => ∏ i, A i (w i) (v i)

/-- `U^{⊗N}`. -/
def tpow (N : ℕ) (U : Matrix Four Four ℂ) : Op N := kronN fun _ => U

theorem kronN_apply {N : ℕ} (A : Fin N → Matrix Four Four ℂ) (w v : Fin N → Four) :
    kronN A w v = ∏ i, A i (w i) (v i) := rfl

theorem kronN_mul {N : ℕ} (A B : Fin N → Matrix Four Four ℂ) :
    kronN A * kronN B = kronN (fun i => A i * B i) := by
  ext w v
  simp only [kronN, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum (fun _ => Finset.univ) (fun i x => A i (w i) x * B i x (v i)),
    Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun u _ => (Finset.prod_mul_distrib).symm

theorem trace_kronN {N : ℕ} (A : Fin N → Matrix Four Four ℂ) :
    (kronN A).trace = ∏ i, (A i).trace := by
  simp only [Matrix.trace, Matrix.diag, kronN, Matrix.of_apply]
  rw [Finset.prod_univ_sum (fun _ => Finset.univ) (fun i x => A i x x), Fintype.piFinset_univ]

theorem kronN_conjTranspose {N : ℕ} (A : Fin N → Matrix Four Four ℂ) :
    (kronN A)ᴴ = kronN (fun i => (A i)ᴴ) := by
  ext w v
  simp only [Matrix.conjTranspose_apply, kronN, Matrix.of_apply]
  rw [star_prod]

theorem kronN_one {N : ℕ} : kronN (fun _ : Fin N => (1 : Matrix Four Four ℂ)) = 1 := by
  ext w v
  simp only [kronN, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.prod_boole]
  congr 1
  exact propext ⟨fun h => funext h, fun h i => by rw [h]⟩

theorem kronN_smul {N : ℕ} (c : Fin N → ℂ) (A : Fin N → Matrix Four Four ℂ) :
    kronN (fun i => c i • A i) = (∏ i, c i) • kronN A := by
  ext w v
  simp only [kronN, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]

theorem tpow_mul (N : ℕ) (U V : Matrix Four Four ℂ) : tpow N U * tpow N V = tpow N (U * V) :=
  kronN_mul _ _

theorem tpow_conjTranspose (N : ℕ) (U : Matrix Four Four ℂ) : (tpow N U)ᴴ = tpow N Uᴴ :=
  kronN_conjTranspose _

theorem tpow_unitary (N : ℕ) (U : Matrix Four Four ℂ) (hU : U * Uᴴ = 1) :
    tpow N U * (tpow N U)ᴴ = 1 := by
  rw [tpow_conjTranspose, tpow_mul, hU, tpow, kronN_one]

/-! ## The strings of the sixteen observables -/

/-- The string `X_{σ₁} ⊗ ⋯ ⊗ X_{σ_N}` of the sixteen observables. -/
noncomputable def pstr {N : ℕ} (σ : Fin N → Fin 16) : Op N := kronN fun i => obs (σ i)

/-- The coefficient of `X` along the string `σ`. -/
noncomputable def coef {N : ℕ} (σ : Fin N → Fin 16) (X : Op N) : ℂ :=
  (pstr σ * X).trace / 4 ^ N

theorem pstr_conjTranspose {N : ℕ} (σ : Fin N → Fin 16) : (pstr σ)ᴴ = pstr σ := by
  rw [pstr, kronN_conjTranspose]
  simp only [obs_conjTranspose]

/-- **The strings are orthogonal:** `Tr(P_σ P_τ) = 4^N δ_στ`. -/
theorem trace_pstr_mul {N : ℕ} (σ τ : Fin N → Fin 16) :
    (pstr σ * pstr τ).trace = if σ = τ then 4 ^ N else 0 := by
  rw [pstr, pstr, kronN_mul, trace_kronN]
  simp only [trace_obs_mul]
  rw [Fintype.prod_ite_zero]
  by_cases h : σ = τ
  · subst h
    simp
  · have h' : ¬ ∀ i, σ i = τ i := fun h'' => h (funext h'')
    simp [h, h']

theorem pstr_linearIndependent (N : ℕ) : LinearIndependent ℂ (pstr (N := N)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg τ
  have h := congrArg (fun M => (pstr τ * M).trace) hg
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    trace_pstr_mul, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Matrix.mul_zero, Matrix.trace_zero] at h
  have h4 : (4 : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_eq_zero.mp h).resolve_right h4

theorem pstr_span (N : ℕ) : Submodule.span ℂ (Set.range (pstr (N := N))) = ⊤ := by
  apply (pstr_linearIndependent N).span_eq_top_of_card_eq_finrank
  rw [Module.finrank_matrix]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Module.finrank_self, one_mul]
  rw [mul_one, ← mul_pow]
  norm_num

/-- **Every operator on `N` systems is `Σ_σ c_σ(X) P_σ`.** -/
theorem expand_pstr {N : ℕ} (X : Op N) : X = ∑ σ, coef σ X • pstr σ := by
  have hX : X ∈ Submodule.span ℂ (Set.range (pstr (N := N))) := (pstr_span N) ▸ Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hX
  obtain ⟨c, hc⟩ := hX
  have key : ∀ τ, coef τ X = c τ := by
    intro τ
    rw [coef, ← hc]
    simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
      trace_pstr_mul, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have h4 : (4 : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  conv_lhs => rw [← hc]
  exact Finset.sum_congr rfl fun σ _ => by rw [key]

/-- An operator all of whose coefficients vanish is zero. -/
theorem eq_zero_of_coef {N : ℕ} (X : Op N) (h : ∀ σ, coef σ X = 0) : X = 0 := by
  rw [expand_pstr X]
  simp [h]

/-! ## Rotations on the strings -/

/-- **Conjugating a string by `U^{⊗N}`**, when `U†X_kU = s_k X_{π k}` on the sixteen. -/
theorem tpow_conj_pstr {N : ℕ} (U : Matrix Four Four ℂ) (s : Fin 16 → ℂ) (π : Fin 16 → Fin 16)
    (hU : ∀ k, Uᴴ * obs k * U = s k • obs (π k)) (σ : Fin N → Fin 16) :
    (tpow N U)ᴴ * pstr σ * tpow N U = (∏ i, s (σ i)) • pstr (π ∘ σ) := by
  rw [tpow_conjTranspose, tpow, tpow, pstr, kronN_mul, kronN_mul]
  simp only [hU]
  rw [kronN_smul]
  rfl

/-- **The coefficients of a kept operator:** if `X` commutes with `U^{⊗N}` for a unitary `U` with
`U†X_kU = s_k X_{π k}`, then `c_σ(X) = (∏ s_{σ_i}) c_{π∘σ}(X)`. -/
theorem coef_of_commute {N : ℕ} (U : Matrix Four Four ℂ) (hu : U * Uᴴ = 1) (s : Fin 16 → ℂ)
    (π : Fin 16 → Fin 16) (hU : ∀ k, Uᴴ * obs k * U = s k • obs (π k)) (X : Op N)
    (hX : X * tpow N U = tpow N U * X) (σ : Fin N → Fin 16) :
    coef σ X = (∏ i, s (σ i)) * coef (π ∘ σ) X := by
  have hW := tpow_unitary N U hu
  have hX' : X = tpow N U * X * (tpow N U)ᴴ := by
    rw [← hX, Matrix.mul_assoc, hW, Matrix.mul_one]
  have h1 : (pstr σ * X).trace = ((tpow N U)ᴴ * pstr σ * tpow N U * X).trace := by
    conv_lhs => rw [hX']
    rw [show pstr σ * (tpow N U * X * (tpow N U)ᴴ) = (pstr σ * tpow N U * X) * (tpow N U)ᴴ by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [coef, coef, h1, tpow_conj_pstr U s π hU, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    mul_div_assoc]

/-! ## Swaps and pairings on `N` systems -/

/-- The operator of a permutation of the systems: `(permOp π)(w, v) = [v = w ∘ π]`. -/
def permOp {N : ℕ} (π : Equiv.Perm (Fin N)) : Op N :=
  Matrix.of fun w v => if v = w ∘ π then 1 else 0

/-- The pairing `E` on the systems `a ≠ b`: `|J⟩⟨J|` on those two, the identity on the others. -/
def Eab {N : ℕ} (a b : Fin N) : Op N :=
  Matrix.of fun w v => if (∀ c, c ≠ a → c ≠ b → w c = v c) then J (w a) (w b) * J (v a) (v b) else 0

/-- The swaps and the pairings of `N` systems. -/
def brauerGens (N : ℕ) : Set (Op N) :=
  {X | ∃ a b : Fin N, a ≠ b ∧ (X = permOp (Equiv.swap a b) ∨ X = Eab a b)}

/-- **The sums of products of swaps and pairings:** the algebra they generate. -/
noncomputable def brauerAlg (N : ℕ) : Subalgebra ℂ (Op N) := Algebra.adjoin ℂ (brauerGens N)

/-- An operator on `N` systems is **kept** by the ten rotations when it commutes with every `U^{⊗N}`,
`U ∈ Sp(2)`. -/
def KeptN (N : ℕ) (X : Op N) : Prop :=
  ∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J → X * tpow N U = tpow N U * X

/-- The kept operators as an algebra. -/
noncomputable def keptAlg (N : ℕ) : Subalgebra ℂ (Op N) where
  carrier := {X | KeptN N X}
  mul_mem' {X Y} hX hY U hu hJ := by
    show X * Y * tpow N U = tpow N U * (X * Y)
    rw [Matrix.mul_assoc, hY U hu hJ, ← Matrix.mul_assoc, hX U hu hJ, Matrix.mul_assoc]
  add_mem' {X Y} hX hY U hu hJ := by
    show (X + Y) * tpow N U = tpow N U * (X + Y)
    rw [Matrix.add_mul, Matrix.mul_add, hX U hu hJ, hY U hu hJ]
  algebraMap_mem' c U hu hJ := by
    show algebraMap ℂ (Op N) c * tpow N U = tpow N U * algebraMap ℂ (Op N) c
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]

theorem mem_keptAlg {N : ℕ} (X : Op N) : X ∈ keptAlg N ↔ KeptN N X := Iff.rfl

theorem permOp_mul_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (A : Op N) (w v : Fin N → Four) :
    (permOp π * A) w v = A (w ∘ π) v := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (w ∘ π)]
  · simp [permOp]
  · intro u _ hu
    simp [permOp, hu]
  · simp

theorem mul_permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (A : Op N) (w v : Fin N → Four) :
    (A * permOp π) w v = A w (v ∘ π.symm) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (v ∘ π.symm)]
  · have h : v = (v ∘ π.symm) ∘ π := by
      funext i
      simp
    simp only [permOp, Matrix.of_apply]
    rw [if_pos h, mul_one]
  · intro u _ hu
    have h : ¬ (v = u ∘ π) := fun h => hu (by rw [h]; funext i; simp)
    simp only [permOp, Matrix.of_apply]
    rw [if_neg h, mul_zero]
  · simp

/-- **Every swap of the systems is kept by every `U^{⊗N}`.** -/
theorem permOp_commute {N : ℕ} (π : Equiv.Perm (Fin N)) (U : Matrix Four Four ℂ) :
    permOp π * tpow N U = tpow N U * permOp π := by
  ext w v
  rw [permOp_mul_apply, mul_permOp_apply]
  simp only [tpow, kronN_apply, Function.comp_apply]
  exact Fintype.prod_equiv π _ _ (fun i => by simp)

/-! ## The pairing `E` on two of `N` systems -/

/-- `w` with the systems `a`, `b` set to `x`, `y`. -/
def upd2 {N : ℕ} (w : Fin N → Four) (a b : Fin N) (x y : Four) : Fin N → Four :=
  Function.update (Function.update w a x) b y

theorem upd2_a {N : ℕ} (w : Fin N → Four) {a b : Fin N} (hab : a ≠ b) (x y : Four) :
    upd2 w a b x y a = x := by
  simp [upd2, Function.update_apply, hab]

theorem upd2_b {N : ℕ} (w : Fin N → Four) (a b : Fin N) (x y : Four) : upd2 w a b x y b = y := by
  simp [upd2]

theorem upd2_other {N : ℕ} (w : Fin N → Four) {a b c : Fin N} (x y : Four) (hca : c ≠ a)
    (hcb : c ≠ b) : upd2 w a b x y c = w c := by
  simp [upd2, Function.update_apply, hca, hcb]

/-- **The sum over the states that agree with `w` off `a` and `b`.** -/
theorem sum_agree {N : ℕ} {a b : Fin N} (hab : a ≠ b) (w : Fin N → Four)
    (f : (Fin N → Four) → ℂ) :
    ∑ u, (if (∀ c, c ≠ a → c ≠ b → w c = u c) then f u else 0) =
      ∑ p : Four × Four, f (upd2 w a b p.1 p.2) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun p => upd2 w a b p.1 p.2) (fun u => (u a, u b))
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro c hca hcb
    exact (upd2_other w p.1 p.2 hca hcb).symm
  · intro u _
    exact Finset.mem_univ _
  · intro p _
    simp [upd2_a w hab, upd2_b]
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    funext c
    by_cases hcb : c = b
    · subst hcb
      exact upd2_b w a c (u a) (u c)
    · by_cases hca : c = a
      · subst hca
        exact upd2_a w hab (u c) (u b)
      · rw [upd2_other w (u a) (u b) hca hcb]
        exact hu c hca hcb
  · intro p _
    rfl

/-- The same sum, with the fixed state on the right. -/
theorem sum_agree' {N : ℕ} {a b : Fin N} (hab : a ≠ b) (v : Fin N → Four)
    (f : (Fin N → Four) → ℂ) :
    ∑ u, (if (∀ c, c ≠ a → c ≠ b → u c = v c) then f u else 0) =
      ∑ p : Four × Four, f (upd2 v a b p.1 p.2) := by
  rw [← sum_agree hab v f]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  exact propext ⟨fun h c hca hcb => (h c hca hcb).symm, fun h c hca hcb => (h c hca hcb).symm⟩

/-- **The product over the systems, with `a`, `b` set to `x`, `y`.** -/
theorem prod_upd2 {N : ℕ} {a b : Fin N} (hab : a ≠ b) (w : Fin N → Four) (x y : Four)
    (g : Fin N → Four → ℂ) :
    ∏ i, g i (upd2 w a b x y i) =
      g a x * (g b y * ∏ i ∈ (Finset.univ.erase a).erase b, g i (w i)) := by
  have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase (Finset.univ.erase a) _ hb, upd2_a w hab, upd2_b]
  congr 2
  refine Finset.prod_congr rfl fun i hi => ?_
  obtain ⟨hib, hi'⟩ := Finset.mem_erase.mp hi
  obtain ⟨hia, -⟩ := Finset.mem_erase.mp hi'
  rw [upd2_other w x y hia hib]

/-- The rest of a product, off the systems `a` and `b`. -/
def restProd {N : ℕ} (a b : Fin N) (U : Matrix Four Four ℂ) (w v : Fin N → Four) : ℂ :=
  ∏ i ∈ (Finset.univ.erase a).erase b, U (w i) (v i)

theorem Eab_mul_tpow {N : ℕ} {a b : Fin N} (hab : a ≠ b) (U : Matrix Four Four ℂ)
    (w v : Fin N → Four) :
    (Eab a b * tpow N U) w v =
      J (w a) (w b) * ((Uᵀ * J * U) (v a) (v b) * restProd a b U w v) := by
  rw [Matrix.mul_apply]
  simp only [Eab, Matrix.of_apply, ite_mul, zero_mul, tpow, kronN_apply]
  rw [sum_agree hab w (fun u => J (w a) (w b) * J (u a) (u b) * ∏ i, U (u i) (v i))]
  simp only [upd2_a w hab, upd2_b, prod_upd2 hab w _ _ (fun i z => U z (v i)), restProd]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  ring

theorem tpow_mul_Eab {N : ℕ} {a b : Fin N} (hab : a ≠ b) (U : Matrix Four Four ℂ)
    (w v : Fin N → Four) :
    (tpow N U * Eab a b) w v =
      J (v a) (v b) * ((U * J * Uᵀ) (w a) (w b) * restProd a b U w v) := by
  rw [Matrix.mul_apply]
  simp only [Eab, Matrix.of_apply, mul_ite, mul_zero, tpow, kronN_apply]
  rw [sum_agree' hab v (fun u => (∏ i, U (w i) (u i)) * (J (u a) (u b) * J (v a) (v b)))]
  simp only [upd2_a v hab, upd2_b, prod_upd2 hab v _ _ (fun i z => U (w i) z), restProd]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  ring

/-- `Uᵀ J U = J` for every unitary `U` with `U J Uᵀ = J`. -/
theorem transpose_keeps_J (U : Matrix Four Four ℂ) (hJ : U * J * Uᵀ = J) : Uᵀ * J * U = J := by
  have hB : U * (J * Uᵀ * (-J)) = 1 := by
    calc U * (J * Uᵀ * (-J)) = -(U * J * Uᵀ * J) := by
          simp only [Matrix.mul_neg, Matrix.mul_assoc]
      _ = 1 := by rw [hJ, J_mul_J, neg_neg]
  have hB' : J * Uᵀ * (-J) * U = 1 := mul_eq_one_comm.mp hB
  calc Uᵀ * J * U = (-(J * J)) * (Uᵀ * J * U) := by rw [J_mul_J, neg_neg, Matrix.one_mul]
    _ = J * (J * Uᵀ * (-J) * U) := by
        simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, neg_neg]
    _ = J := by rw [hB', Matrix.mul_one]

/-- **The pairing `E` of two of `N` systems is kept by every rotation of `Sp(2)`.** -/
theorem Eab_commute {N : ℕ} {a b : Fin N} (hab : a ≠ b) (U : Matrix Four Four ℂ)
    (hJ : U * J * Uᵀ = J) : Eab a b * tpow N U = tpow N U * Eab a b := by
  ext w v
  rw [Eab_mul_tpow hab, tpow_mul_Eab hab, transpose_keeps_J U hJ, hJ]
  ring

/-- **The easy half of Proposition 15, for every `N`:** every sum of products of swaps and pairings is
kept by every rotation of `Sp(2)`. -/
theorem brauer_kept (N : ℕ) : brauerAlg N ≤ keptAlg N := by
  apply Algebra.adjoin_le
  rintro X ⟨a, b, hab, rfl | rfl⟩
  · show KeptN N (permOp (Equiv.swap a b))
    exact fun U _ _ => permOp_commute _ U
  · show KeptN N (Eab a b)
    exact fun U _ hJ => Eab_commute hab U hJ

/-! ## One system and two systems -/

/-- The operators on one system kept by the ten rotations. -/
def keptOne : Submodule ℂ (Matrix Four Four ℂ) where
  carrier := {X | ∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J → X * U = U * X}
  add_mem' {X Y} hX hY U hu hJ := by rw [Matrix.add_mul, Matrix.mul_add, hX U hu hJ, hY U hu hJ]
  zero_mem' U _ _ := by simp
  smul_mem' c X hX U hu hJ := by rw [Matrix.smul_mul, Matrix.mul_smul, hX U hu hJ]

/-- The operators on two systems kept by the ten rotations. -/
def keptTwo : Submodule ℂ (Matrix Two Two ℂ) where
  carrier := {X | ∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J →
    X * (U ⊗ₖ U) = (U ⊗ₖ U) * X}
  add_mem' {X Y} hX hY U hu hJ := by rw [Matrix.add_mul, Matrix.mul_add, hX U hu hJ, hY U hu hJ]
  zero_mem' U _ _ := by simp
  smul_mem' c X hX U hu hJ := by rw [Matrix.smul_mul, Matrix.mul_smul, hX U hu hJ]

theorem keptOne_eq : keptOne = Submodule.span ℂ {(1 : Matrix Four Four ℂ)} := by
  apply le_antisymm
  · intro X hX
    rw [Comparison.Article.commutant_one X hX]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    show ∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J →
      (1 : Matrix Four Four ℂ) * U = U * 1
    intro U _ _
    rw [Matrix.one_mul, Matrix.mul_one]

theorem finrank_keptOne : finrank ℂ keptOne = 1 := by
  rw [keptOne_eq, finrank_span_singleton one_ne_zero]

theorem one_swap_E_linearIndependent :
    LinearIndependent ℂ ![(1 : Matrix Two Two ℂ), swap, Eop] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hg
  obtain ⟨h0, h1, h2⟩ := Comparison.Article.one_swap_E_independent _ _ _ hg
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem keptTwo_eq : keptTwo = Submodule.span ℂ (Set.range ![(1 : Matrix Two Two ℂ), swap, Eop]) := by
  apply le_antisymm
  · intro X hX
    have h := Comparison.Article.commutant_two X hX
    rw [Submodule.mem_span_range_iff_exists_fun]
    set x0 := star (rel 0) ⬝ᵥ (X *ᵥ rel 0)
    set xF := star (rel 6) ⬝ᵥ (X *ᵥ rel 6)
    set xL := star (rel 1) ⬝ᵥ (X *ᵥ rel 1)
    refine ⟨![(xF + xL) / 2, (xF - xL) / 2, (x0 - xL) / 4], ?_⟩
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [h]
    module
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show ∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J →
      ![(1 : Matrix Two Two ℂ), swap, Eop] i * (U ⊗ₖ U) =
        (U ⊗ₖ U) * ![(1 : Matrix Two Two ℂ), swap, Eop] i
    intro U hu hJ
    fin_cases i
    · simp
    · exact kron_swap_comm U |>.symm
    · exact Sp2_comm_Eop U hu hJ

theorem finrank_keptTwo : finrank ℂ keptTwo = 3 := by
  rw [keptTwo_eq, finrank_span_eq_card one_swap_E_linearIndependent]
  simp

end Geometry

open Comparison.System.Geometry

/-- **Proposition 15 (swaps and the singlet make every kept operator), the parts proved.** For every
number `N` of systems, every swap `P_π` and every pairing `E_ab` (`|J⟩⟨J|` on the systems `a ≠ b`, the
singlet between them), and so every sum of products of them, commutes with every `U^{⊗N}`,
`U ∈ Sp(2)`; on one system the kept operators are the multiples of `1`, dimension 1; on two systems they
are `a + bP + cE`, with `1, P, E` independent, dimension 3. The converse on three and four systems, with the
dimensions 14 and 84, is `prop_15` (`System/Geometry/KeptAll.lean`); every `N ≥ 5`, the first fundamental theorem of
invariant theory for `Sp(2)`, is the statement that completes Prop. 15. Recognition: none. -/
theorem Geometry.kept_up_to_two :
    (∀ N : ℕ, ∀ X ∈ brauerAlg N, KeptN N X) ∧
    (∀ (N : ℕ) (π : Equiv.Perm (Fin N)), KeptN N (permOp π)) ∧
    (∀ (N : ℕ) (a b : Fin N), a ≠ b → KeptN N (Eab a b)) ∧
    keptOne = Submodule.span ℂ {(1 : Matrix Four Four ℂ)} ∧ finrank ℂ keptOne = 1 ∧
    keptTwo = Submodule.span ℂ (Set.range ![(1 : Matrix Two Two ℂ), swap, Eop]) ∧
    LinearIndependent ℂ ![(1 : Matrix Two Two ℂ), swap, Eop] ∧ finrank ℂ keptTwo = 3 :=
  ⟨fun N X hX => brauer_kept N hX, fun N π U _ _ => permOp_commute π U,
    fun N a b hab U _ hJ => Eab_commute hab U hJ, keptOne_eq, finrank_keptOne, keptTwo_eq,
    one_swap_E_linearIndependent, finrank_keptTwo⟩

end Comparison.System
