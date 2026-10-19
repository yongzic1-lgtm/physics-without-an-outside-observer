import Comparison.System.Existence.Ext.Commutant
import Comparison.System.Existence.Line
import Comparison.GroupsContinuumLaw.Centres

/-!
# The proof system, the existence layer: the rotations of a pair and what each keeps (Proposition 46)

The ten lines of a pair on `H ⊗ H ⊗ ℂ²` (`tenLine`) and the ten lines on `Λℂ⁵`
(`SysExt.fockLine`) are one representation: `W f_S = c_S Ω₊`, `c_S` the ordered product of the creation steps
`c_t = (Γ_t − iΓ_{5+t})/2` over `S` and `Ω₊ = Ω ⊗ e₊`, intertwines the creation and the annihilation steps
(`W ε_t = c_t W`, `W ι_t = a_t W`), hence the ten lines and all their rotations, and is a bijection. So the chain
`45, 25, 24, 12, 9` of `SysExt.turns_chain`, proved on `Λℂ⁵`, is the chain of the rotations of the pair on the
two-spinor states: keeping the comparison, the singlet `Ω`, the plane count `N_F` and the last-step direction's two-spinor state `ℓ_h`.
-/

namespace Comparison.System.Existence

open Matrix Complex Kronecker

/-- The vectors of the pair, `H ⊗ H ⊗ ℂ²`. -/
abbrev PairV := Two × Fin 2 → ℂ

/-- The operators of the pair. -/
abbrev PairM := Matrix (Two × Fin 2) (Two × Fin 2) ℂ

/-! ## Creation and annihilation in the pair -/

/-- The creation step of the line `t`: `c_t = (Γ_t − iΓ_{5+t})/2`. -/
noncomputable def crP (t : Fin 5) : PairM := (1 / 2 : ℂ) • (tenLine (Sum.inl t) - I • tenLine (Sum.inr t))

/-- The annihilation step of the line `t`: `a_t = (Γ_t + iΓ_{5+t})/2`. -/
noncomputable def anP (t : Fin 5) : PairM := (1 / 2 : ℂ) • (tenLine (Sum.inl t) + I • tenLine (Sum.inr t))

theorem tenLine_inl_eq (t : Fin 5) : tenLine (Sum.inl t) = crP t + anP t := by
  rw [crP, anP, ← smul_add,
    show tenLine (Sum.inl t) - I • tenLine (Sum.inr t) + (tenLine (Sum.inl t) + I • tenLine (Sum.inr t)) =
      (2 : ℂ) • tenLine (Sum.inl t) by module, smul_smul]
  norm_num

theorem tenLine_inr_eq (t : Fin 5) : tenLine (Sum.inr t) = I • (crP t - anP t) := by
  rw [crP, anP, ← smul_sub,
    show tenLine (Sum.inl t) - I • tenLine (Sum.inr t) - (tenLine (Sum.inl t) + I • tenLine (Sum.inr t)) =
      (-2 * I) • tenLine (Sum.inr t) by module, smul_smul, smul_smul]
  have : I * (1 / 2) * (-2 * I) = 1 := by
    ring_nf
    rw [I_sq]
    ring
  rw [this, one_smul]

section CAR

variable (s t : Fin 5)

local notation "a" => tenLine (Sum.inl s)
local notation "a'" => tenLine (Sum.inr s)
local notation "b" => tenLine (Sum.inl t)
local notation "b'" => tenLine (Sum.inr t)

theorem crP_expand : crP s * crP t + crP t * crP s = (1 / 4 : ℂ) •
    ((a * b + b * a) - I • (a * b' + b' * a) - I • (a' * b + b * a') + (I * I) • (a' * b' + b' * a')) := by
  simp only [crP, smul_mul_smul_comm, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add,
    smul_smul]
  module

theorem anP_expand : anP s * anP t + anP t * anP s = (1 / 4 : ℂ) •
    ((a * b + b * a) + I • (a * b' + b' * a) + I • (a' * b + b * a') + (I * I) • (a' * b' + b' * a')) := by
  simp only [anP, smul_mul_smul_comm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  module

theorem anP_crP_expand : anP s * crP t + crP t * anP s = (1 / 4 : ℂ) •
    ((a * b + b * a) - I • (a * b' + b' * a) + I • (a' * b + b * a') - (I * I) • (a' * b' + b' * a')) := by
  simp only [anP, crP, smul_mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_sub, smul_smul]
  module

end CAR

theorem crP_anticomm (s t : Fin 5) : crP s * crP t + crP t * crP s = 0 := by
  rw [crP_expand, tenLine_clifford, tenLine_clifford, tenLine_clifford, tenLine_clifford]
  simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, smul_zero, sub_zero, I_mul_I]
  split_ifs <;> module

theorem anP_anticomm (s t : Fin 5) : anP s * anP t + anP t * anP s = 0 := by
  rw [anP_expand, tenLine_clifford, tenLine_clifford, tenLine_clifford, tenLine_clifford]
  simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, smul_zero, add_zero, I_mul_I]
  split_ifs <;> module

theorem anP_crP (s t : Fin 5) : anP s * crP t + crP t * anP s = if s = t then 1 else 0 := by
  rw [anP_crP_expand, tenLine_clifford, tenLine_clifford, tenLine_clifford, tenLine_clifford]
  simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, smul_zero, sub_zero, add_zero, I_mul_I]
  split_ifs <;> module

theorem crP_sq (t : Fin 5) : crP t * crP t = 0 := by
  have h := crP_anticomm t t
  rw [← two_smul ℂ] at h
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

theorem crP_anti {s t : Fin 5} (_ : s ≠ t) : crP s * crP t = -(crP t * crP s) :=
  eq_neg_of_add_eq_zero_left (crP_anticomm s t)

/-! ## The singlet of the pair -/

/-- The product vector `x ⊗ y`. -/
def kronVec {m n : Type*} (x : m → ℂ) (y : n → ℂ) : m × n → ℂ := fun q => x q.1 * y q.2

theorem kron_mulVec_kronVec {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (x : m → ℂ) (y : n → ℂ) : (A ⊗ₖ B) *ᵥ kronVec x y = kronVec (A *ᵥ x) (B *ᵥ y) := by
  funext q
  simp only [Matrix.mulVec, dotProduct, kronVec, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem kronVec_smul_right {m n : Type*} (x : m → ℂ) (c : ℂ) (y : n → ℂ) :
    kronVec x (c • y) = c • kronVec x y := by
  funext q
  simp only [kronVec, Pi.smul_apply, smul_eq_mul]
  ring

/-- **`Ω₊ = Ω ⊗ e₊`**, the singlet of the pair on the two-spinor states' half. -/
noncomputable def vacP : PairV := kronVec Ω (Pi.single 0 1)

theorem σ₁_e₀ : σ₁ *ᵥ (Pi.single 0 1 : Fin 2 → ℂ) = Pi.single 1 1 := by
  funext i
  fin_cases i <;> simp [σ₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]

theorem σ₂_e₀ : σ₂ *ᵥ (Pi.single 0 1 : Fin 2 → ℂ) = I • Pi.single 1 1 := by
  funext i
  fin_cases i <;> simp [σ₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]

/-- **Every annihilation step kills the singlet of the pair:** `a_t Ω₊ = 0`. -/
theorem anP_vac (t : Fin 5) : anP t *ᵥ vacP = 0 := by
  rw [anP, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, vacP]
  simp only [tenLine]
  rw [kron_mulVec_kronVec, kron_mulVec_kronVec, σ₁_e₀, σ₂_e₀, same_from_either_thing, kronVec_smul_right,
    smul_smul, I_mul_I, neg_one_smul, add_neg_cancel, smul_zero]

theorem vacP_ne : vacP ≠ 0 := by
  intro h
  have h1 : ∀ p : Two, vacP (p, 0) = Ω p := by
    intro p
    simp [vacP, kronVec]
  have hΩ : Ω = 0 := by
    funext p
    rw [← h1 p, h]
    rfl
  have := Ω_norm
  rw [hΩ] at this
  simp at this

/-! ## The map `W` from `Λℂ⁵` to the pair -/

/-- `W f_S = c_S Ω₊`. -/
noncomputable def wS (S : Finset (Fin 5)) : PairV := SysExt.ordProd crP S *ᵥ vacP

theorem wS_empty : wS ∅ = vacP := by
  rw [wS, SysExt.ordProd_empty, Matrix.one_mulVec]

theorem smul_one_mul_mulVec (c : ℂ) (M : PairM) (v : PairV) : ((c • (1 : PairM)) * M) *ᵥ v = c • (M *ᵥ v) := by
  rw [smul_mul_assoc, Matrix.one_mul, Matrix.smul_mulVec]

theorem neg_one_pow_eq (k : ℕ) : (-1 : PairM) ^ k = ((-1 : ℂ) ^ k) • (1 : PairM) := by
  rw [show (-1 : PairM) = (-1 : ℂ) • (1 : PairM) by simp, smul_pow, one_pow]

/-- **`c_t W f_S = W ε_t f_S`:** `0` for `t ∈ S`, `(−1)^{#{c ∈ S : c < t}} W f_{S ∪ {t}}` otherwise. -/
theorem crP_wS (t : Fin 5) (S : Finset (Fin 5)) :
    crP t *ᵥ wS S = if t ∈ S then 0 else SysExt.extSign (R := ℂ) t S • wS (insert t S) := by
  have h := SysExt.ordProd_mul_left crP (fun _ => (0 : PairM)) (fun a b hab => crP_anti hab) crP_sq
    (fun _ _ => Commute.zero_left _) S t
  rw [wS, Matrix.mulVec_mulVec, h, neg_one_pow_eq, SysExt.extSign_eq]
  split_ifs with ht
  · rw [zero_mul, mul_zero, Matrix.zero_mulVec]
  · rw [smul_one_mul_mulVec]
    rfl

/-- **`a_t W f_S = W ι_t f_S`:** `(−1)^{#{c ∈ S : c < t}} W f_{S ∖ {t}}` for `t ∈ S`, `0` otherwise. -/
theorem anP_wS (t : Fin 5) (S : Finset (Fin 5)) :
    anP t *ᵥ wS S = if t ∈ S then SysExt.extSign (R := ℂ) t (S.erase t) • wS (S.erase t) else 0 := by
  induction S using Finset.induction_on_min generalizing t with
  | empty =>
    rw [wS_empty, anP_vac]
    simp
  | insert m S hm ih =>
    have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
    have hw : wS (insert m S) = crP m *ᵥ wS S := by
      rw [wS, SysExt.ordProd_insert_min _ hm, ← Matrix.mulVec_mulVec, ← wS]
    have hac : anP t * crP m = (if t = m then 1 else 0) - crP m * anP t := by
      rw [← anP_crP t m]
      abel
    rw [hw, Matrix.mulVec_mulVec, hac, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ih t]
    by_cases htm : t = m
    · subst htm
      have h1 : t ∈ insert t S := Finset.mem_insert_self t S
      rw [if_pos rfl, Matrix.one_mulVec, if_neg hmS, Matrix.mulVec_zero, sub_zero, if_pos h1,
        Finset.erase_insert hmS, SysExt.extSign_of_min hm, one_smul]
    · rw [if_neg htm, Matrix.zero_mulVec, zero_sub]
      by_cases htS : t ∈ S
      · have h1 : t ∈ insert m S := Finset.mem_insert_of_mem htS
        have hmE : m ∉ S.erase t := fun h => hmS (Finset.mem_of_mem_erase h)
        have hmin : ∀ x ∈ S.erase t, m < x := fun x hx => hm x (Finset.mem_of_mem_erase hx)
        have hmt : m < t := hm t htS
        rw [if_pos htS, Matrix.mulVec_smul, crP_wS, if_neg hmE, SysExt.extSign_of_min hmin, one_smul,
          if_pos h1, Finset.erase_insert_of_ne (Ne.symm htm), SysExt.extSign_insert hmE, if_pos hmt,
          neg_one_mul, neg_smul]
      · have h1 : t ∉ insert m S := by
          rw [Finset.mem_insert]
          rintro (h | h)
          · exact htm h
          · exact htS h
        rw [if_neg htS, if_neg h1, Matrix.mulVec_zero, neg_zero]

/-- The number operator of the line `t` on `W f_S`: `c_ta_t W f_S = [t ∈ S] W f_S`. -/
theorem numP_wS (t : Fin 5) (S : Finset (Fin 5)) :
    (crP t * anP t) *ᵥ wS S = (if t ∈ S then (1 : ℂ) else 0) • wS S := by
  rw [← Matrix.mulVec_mulVec, anP_wS]
  split_ifs with ht
  · rw [Matrix.mulVec_smul, crP_wS, if_neg (Finset.notMem_erase t S), smul_smul, SysExt.extSign_mul_self,
      one_smul, Finset.insert_erase ht, one_smul]
  · rw [Matrix.mulVec_zero, zero_smul]

theorem wS_ne (S : Finset (Fin 5)) : wS S ≠ 0 := by
  induction S using Finset.induction_on_min with
  | empty => rw [wS_empty]; exact vacP_ne
  | insert m S hm ih =>
    intro h
    have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
    have := anP_wS m (insert m S)
    rw [h, Matrix.mulVec_zero, if_pos (Finset.mem_insert_self m S), Finset.erase_insert hmS,
      SysExt.extSign_of_min hm, one_smul] at this
    exact ih this.symm

/-- The weighted count `K = Σ_t 2^t c_ta_t`. -/
noncomputable def weightP : PairM := ∑ t : Fin 5, ((2 : ℂ) ^ (t : ℕ)) • (crP t * anP t)

/-- The weight of a set, `Σ_{t ∈ S} 2^t`. -/
def setWeight (S : Finset (Fin 5)) : ℕ := ∑ t ∈ S, 2 ^ (t : ℕ)

theorem setWeight_injective : Function.Injective setWeight := by
  decide +kernel

theorem weightP_wS (S : Finset (Fin 5)) : weightP *ᵥ wS S = ((setWeight S : ℕ) : ℂ) • wS S := by
  rw [weightP, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, numP_wS, smul_smul]
  rw [← Finset.sum_smul, setWeight]
  congr 1
  push_cast
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem wS_linearIndependent : LinearIndependent ℂ wS := by
  refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' weightP)
    (fun S => ((setWeight S : ℕ) : ℂ)) ?_ wS fun S => ?_
  · intro S T h
    have h' : ((setWeight S : ℕ) : ℂ) = setWeight T := h
    exact setWeight_injective (by exact_mod_cast h')
  · refine ⟨?_, wS_ne S⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, weightP_wS]

/-- **`W`**, from `Λℂ⁵` to the pair. -/
noncomputable def Wmap : (Finset (Fin 5) → ℂ) →ₗ[ℂ] PairV :=
  Matrix.toLin' (Matrix.of fun q S => wS S q)

theorem Wmap_single (S : Finset (Fin 5)) : Wmap (Pi.single S 1) = wS S := by
  rw [Wmap, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

theorem Wmap_apply (f : Finset (Fin 5) → ℂ) : Wmap f = ∑ S, f S • wS S := by
  conv_lhs => rw [show f = ∑ S, f S • (Pi.single S 1 : Finset (Fin 5) → ℂ) by
    funext T; simp [Finset.sum_apply, Pi.single_apply]]
  simp only [map_sum, map_smul, Wmap_single]

theorem Wmap_injective : Function.Injective Wmap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  rw [Wmap_apply] at hf
  have := (Fintype.linearIndependent_iff.mp wS_linearIndependent) f hf
  funext S
  exact this S

theorem Wmap_bijective : Function.Bijective Wmap := by
  refine ⟨Wmap_injective, ?_⟩
  have hdim : Module.finrank ℂ (Finset (Fin 5) → ℂ) = Module.finrank ℂ PairV := by
    simp [Module.finrank_fintype_fun_eq_card, Fintype.card_finset, Fintype.card_prod]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp Wmap_injective

/-! ## `W` intertwines the ten lines and their rotations -/

theorem W_εx (t : Fin 5) (v : Finset (Fin 5) → ℂ) : Wmap (SysExt.εx t v) = crP t *ᵥ Wmap v := by
  have h : Wmap ∘ₗ SysExt.εx t = Matrix.toLin' (crP t) ∘ₗ Wmap := by
    refine LinearMap.pi_ext' fun S => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.toLin'_apply, Wmap_single]
    rw [SysExt.εx_single, crP_wS]
    split_ifs
    · simp
    · rw [map_smul, Wmap_single]
  have := LinearMap.congr_fun h v
  simpa only [LinearMap.comp_apply, Matrix.toLin'_apply] using this

theorem W_ιx (t : Fin 5) (v : Finset (Fin 5) → ℂ) : Wmap (SysExt.ιx t v) = anP t *ᵥ Wmap v := by
  have h : Wmap ∘ₗ SysExt.ιx t = Matrix.toLin' (anP t) ∘ₗ Wmap := by
    refine LinearMap.pi_ext' fun S => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.toLin'_apply, Wmap_single]
    rw [SysExt.ιx_single, anP_wS]
    split_ifs
    · rw [map_smul, Wmap_single]
    · simp
  have := LinearMap.congr_fun h v
  simpa only [LinearMap.comp_apply, Matrix.toLin'_apply] using this

/-- **`W` intertwines the ten lines:** `W Γ^Λ_x = Γ_x W`. -/
theorem W_line (x : SysExt.Ten) (v : Finset (Fin 5) → ℂ) :
    Wmap (SysExt.fockLine x v) = tenLine x *ᵥ Wmap v := by
  rcases x with t | t
  · simp only [SysExt.fockLine, LinearMap.add_apply, map_add, W_εx, W_ιx]
    rw [tenLine_inl_eq, Matrix.add_mulVec]
  · simp only [SysExt.fockLine, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub, W_εx, W_ιx]
    rw [tenLine_inr_eq, Matrix.smul_mulVec, Matrix.sub_mulVec]

/-- **`W` intertwines every rotation:** `W ρ^Λ(M) = ρ(M) W`. -/
theorem W_turn (M : Matrix SysExt.Ten SysExt.Ten ℝ) (v : Finset (Fin 5) → ℂ) :
    Wmap (SysExt.turnOf SysExt.fockLine M v) = SysExt.turnOf tenLine M *ᵥ Wmap v := by
  rw [SysExt.turnOf_apply, SysExt.turnOf_apply]
  simp only [LinearMap.sum_apply, map_sum, Matrix.sum_mulVec, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.map_smul_of_tower, W_line, Matrix.smul_mulVec, Matrix.mulVec_mulVec]

theorem W_planeN (v : Finset (Fin 5) → ℂ) :
    Wmap (SysExt.planeN v) = (crP 3 * anP 3 + crP 4 * anP 4) *ᵥ Wmap v := by
  simp only [SysExt.planeN, LinearMap.add_apply, Module.End.mul_apply, map_add, W_εx, W_ιx, Matrix.add_mulVec,
    Matrix.mulVec_mulVec]

theorem W_vacF : Wmap SysExt.vacF = vacP := by
  rw [SysExt.vacF, Wmap_single, wS_empty]

theorem W_lastDirection : Wmap SysExt.lastDirectionRelVec = wS {0, 1, 2, 4} := by
  rw [SysExt.lastDirectionRelVec, Wmap_single]

theorem keep_vec_iff (M : Matrix SysExt.Ten SysExt.Ten ℝ) (f : Finset (Fin 5) → ℂ) :
    SysExt.turnOf tenLine M *ᵥ Wmap f = 0 ↔ SysExt.turnOf SysExt.fockLine M f = 0 := by
  rw [← W_turn, LinearMap.map_eq_zero_iff Wmap Wmap_injective]

theorem comm_transfer {XF NF : SysExt.FockE} {XP NP : PairM}
    (hX : ∀ v, Wmap (XF v) = XP *ᵥ Wmap v) (hN : ∀ v, Wmap (NF v) = NP *ᵥ Wmap v) :
    XP * NP = NP * XP ↔ XF * NF = NF * XF := by
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    apply Wmap_injective
    rw [Module.End.mul_apply, Module.End.mul_apply, hX, hN, hN, hX, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  · intro h
    have key : ∀ w, (XP * NP) *ᵥ w = (NP * XP) *ᵥ w := by
      intro w
      obtain ⟨v, rfl⟩ := Wmap_bijective.2 w
      rw [← Matrix.mulVec_mulVec, ← hN, ← hX, ← Module.End.mul_apply, h, Module.End.mul_apply, hN, hX,
        Matrix.mulVec_mulVec]
    exact Matrix.toLin'.injective (LinearMap.ext fun w => by simpa only [Matrix.toLin'_apply] using key w)

/-! ## The plane count and the last-step direction's two-spinor state on the two-spinor states -/

theorem kronVec_e₀_σ₃ (r : Two → ℂ) (G : Matrix Two Two ℂ) :
    (G ⊗ₖ σ₃) *ᵥ kronVec r (Pi.single 0 1) = kronVec (G *ᵥ r) (Pi.single 0 1) := by
  rw [kron_mulVec_kronVec]
  congr 1
  funext i
  fin_cases i <;> simp [σ₃, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]

/-- **The number operator of a line on the pair:** `c_ta_t = ½(1 − (γ_t ⊗ γ_t) ⊗ σ_z)`: on the two-spinor states
(`σ_z = +1`) the count `(1 − γ_t ⊗ γ_t)/2` of the disagreement on the line `t`. -/
theorem numP_eq (t : Fin 5) :
    crP t * anP t = (1 / 2 : ℂ) • (1 - (γ t ⊗ₖ γ t) ⊗ₖ σ₃) := by
  have h1 := tenLine_clifford (Sum.inl t) (Sum.inl t)
  have h4 := tenLine_clifford (Sum.inr t) (Sum.inr t)
  have h2 := tenLine_clifford (Sum.inl t) (Sum.inr t)
  simp only [if_true, reduceCtorEq, if_false] at h1 h2 h4
  have hsq1 : tenLine (Sum.inl t) * tenLine (Sum.inl t) = 1 := by
    rw [← two_smul ℂ] at h1
    exact smul_right_injective PairM two_ne_zero h1
  have hsq4 : tenLine (Sum.inr t) * tenLine (Sum.inr t) = 1 := by
    rw [← two_smul ℂ] at h4
    exact smul_right_injective PairM two_ne_zero h4
  have hanti : tenLine (Sum.inr t) * tenLine (Sum.inl t) = -(tenLine (Sum.inl t) * tenLine (Sum.inr t)) :=
    eq_neg_of_add_eq_zero_right h2
  have e : tenLine (Sum.inl t) * tenLine (Sum.inr t) = (I • (γ t ⊗ₖ γ t)) ⊗ₖ σ₃ := by
    simp only [tenLine, kron3_mul, Matrix.mul_one, Matrix.one_mul, σ₁σ₂_eq, Matrix.kronecker_smul,
      Matrix.smul_kronecker]
  have expand : crP t * anP t = (1 / 4 : ℂ) • (tenLine (Sum.inl t) * tenLine (Sum.inl t) +
      I • (tenLine (Sum.inl t) * tenLine (Sum.inr t)) - I • (tenLine (Sum.inr t) * tenLine (Sum.inl t)) +
      (-(I * I)) • (tenLine (Sum.inr t) * tenLine (Sum.inr t))) := by
    simp only [crP, anP, smul_mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      smul_add, smul_sub, smul_smul]
    module
  rw [expand, hsq1, hsq4, hanti, e, Matrix.smul_kronecker]
  simp only [smul_neg, sub_neg_eq_add, smul_smul, I_mul_I]
  module

/-- The plane count of the pair, `N_F = c_ha_h + c_ka_k` at the plane `{h, k} = {3, 4}`. -/
noncomputable def planeNP : PairM := crP 3 * anP 3 + crP 4 * anP 4

theorem planeNP_eq : planeNP = (1 / 2 : ℂ) • (1 - (γ 3 ⊗ₖ γ 3) ⊗ₖ σ₃) + (1 / 2 : ℂ) • (1 - (γ 4 ⊗ₖ γ 4) ⊗ₖ σ₃) := by
  rw [planeNP, numP_eq, numP_eq]

theorem neg_kron {m n p q : Type*} (A : Matrix m n ℂ) (B : Matrix p q ℂ) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext i j
  simp [Matrix.kroneckerMap_apply]

theorem gamma_kron_ell (t : Fin 5) : (γ t ⊗ₖ γ t) *ᵥ ell 3 = if t = 3 then ell 3 else -ell 3 := by
  have hX : ∀ X : Matrix Four Four ℂ, (γ t ⊗ₖ γ t) *ᵥ ((X ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω) =
      ((γ t * X * γ t) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω := by
    intro X
    have e1 : γ t ⊗ₖ γ t = ((γ t) ⊗ₖ (1 : Matrix Four Four ℂ)) * ((1 : Matrix Four Four ℂ) ⊗ₖ γ t) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    have e2 : (1 : Matrix Four Four ℂ) ⊗ₖ γ t * (X ⊗ₖ (1 : Matrix Four Four ℂ)) =
        (X ⊗ₖ (1 : Matrix Four Four ℂ)) * ((1 : Matrix Four Four ℂ) ⊗ₖ γ t) := by
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, Matrix.mul_one]
    rw [e1, Matrix.mulVec_mulVec, Matrix.mul_assoc, e2, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      same_from_either_thing, Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul]
  rw [ell, hX]
  split_ifs with ht
  · subst ht
    rw [γ_mul_self, Matrix.one_mul]
  · rw [γ_anticomm ht, Matrix.neg_mul, Matrix.mul_assoc, γ_mul_self, Matrix.mul_one, neg_kron,
      Matrix.neg_mulVec]

/-- **The last-step direction's two-spinor state of the pair**, `ℓ_h ⊗ e₊` (`h = 3`). -/
noncomputable def lastDirectionP : PairV := kronVec (ell 3) (Pi.single 0 1)

theorem numP_lastDirectionP (t : Fin 5) :
    (crP t * anP t) *ᵥ lastDirectionP = (if t ∈ ({0, 1, 2, 4} : Finset (Fin 5)) then (1 : ℂ) else 0) • lastDirectionP := by
  rw [numP_eq, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, lastDirectionP, kronVec_e₀_σ₃, gamma_kron_ell]
  have hmem : (t ∈ ({0, 1, 2, 4} : Finset (Fin 5))) ↔ t ≠ 3 := by
    revert t
    decide
  by_cases ht : t = 3
  · have : t ∉ ({0, 1, 2, 4} : Finset (Fin 5)) := fun h => (hmem.mp h) ht
    rw [if_pos ht, if_neg this, sub_self, smul_zero, zero_smul]
  · have : t ∈ ({0, 1, 2, 4} : Finset (Fin 5)) := hmem.mpr ht
    rw [if_neg ht, if_pos this, one_smul]
    funext q
    simp only [kronVec, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    ring

theorem lastDirectionP_ne : lastDirectionP ≠ 0 := by
  intro h
  have h1 : ∀ p : Two, lastDirectionP (p, 0) = ell 3 p := by
    intro p
    simp [lastDirectionP, kronVec]
  have hl : ell 3 = 0 := by
    funext p
    rw [← h1 p, h]
    rfl
  have hn := rel_inner (lineIdx 3) (lineIdx 3)
  rw [← ell_eq_rel 3, hl] at hn
  simp at hn

/-- **A joint eigenvector of the five number operators is a multiple of one `W f_T`.** -/
theorem joint_eigen (T : Finset (Fin 5)) (v : PairV)
    (hv : ∀ t, (crP t * anP t) *ᵥ v = (if t ∈ T then (1 : ℂ) else 0) • v) : ∃ c : ℂ, v = c • wS T := by
  obtain ⟨f, rfl⟩ := Wmap_bijective.2 v
  refine ⟨f T, ?_⟩
  have hf : ∀ S, S ≠ T → f S = 0 := by
    intro S hST
    obtain ⟨t, ht⟩ : ∃ t, ¬(t ∈ S ↔ t ∈ T) := by
      by_contra hcon
      push_neg at hcon
      exact hST (Finset.ext hcon)
    have key := hv t
    rw [Wmap_apply, Matrix.mulVec_sum] at key
    simp only [Matrix.mulVec_smul, numP_wS, smul_smul, Finset.smul_sum] at key
    have hz : ∑ S, (f S * (if t ∈ S then (1 : ℂ) else 0) - (if t ∈ T then (1 : ℂ) else 0) * f S) • wS S = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, key, sub_self]
    have hS := Fintype.linearIndependent_iff.mp wS_linearIndependent _ hz S
    by_cases h1 : t ∈ S
    · have h2 : t ∉ T := fun h2 => ht ⟨fun _ => h2, fun _ => h1⟩
      simpa [h1, h2] using hS
    · have h2 : t ∈ T := by
        by_contra h2
        exact ht ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      simpa [h1, h2] using hS
  rw [Wmap_apply, Finset.sum_eq_single T (fun S _ hS => by rw [hf S hS, zero_smul]) (by simp)]

theorem lastDirectionP_eq : ∃ c : ℂ, c ≠ 0 ∧ lastDirectionP = c • wS {0, 1, 2, 4} := by
  obtain ⟨c, hc⟩ := joint_eigen {0, 1, 2, 4} lastDirectionP numP_lastDirectionP
  refine ⟨c, fun h0 => lastDirectionP_ne (by rw [hc, h0, zero_smul]), hc⟩

/-! ## The chain on the pair -/

/-- The operators of the pair that kill the vector `v` (keep the two-spinor state `v`). -/
def annihP (v : PairV) : Submodule ℝ PairM where
  carrier := {X | X *ᵥ v = 0}
  add_mem' {X Y} hX hY := by
    change X *ᵥ v = 0 at hX
    change Y *ᵥ v = 0 at hY
    change (X + Y) *ᵥ v = 0
    rw [Matrix.add_mulVec, hX, hY, add_zero]
  zero_mem' := by
    change (0 : PairM) *ᵥ v = 0
    exact Matrix.zero_mulVec v
  smul_mem' c X hX := by
    change X *ᵥ v = 0 at hX
    change (c • X) *ᵥ v = 0
    rw [Matrix.smul_mulVec, hX, smul_zero]

theorem mem_annihP (v : PairV) (X : PairM) : X ∈ annihP v ↔ X *ᵥ v = 0 := Iff.rfl

/-- The rotations of the pair that keep the comparison. -/
noncomputable def keepLP : Submodule ℝ PairM :=
  SysExt.turnsTen tenLine ⊓ SysExt.commWith (SysExt.pairSum tenLine)

/-- … that keep also the singlet `Ω₊`. -/
noncomputable def keepVacP : Submodule ℝ PairM := keepLP ⊓ annihP vacP

/-- … that keep also the plane count `N_F`. -/
noncomputable def keepPlaneP : Submodule ℝ PairM := keepVacP ⊓ SysExt.commWith planeNP

/-- … that keep also the last-step direction's two-spinor state `ℓ_h ⊗ e₊`. -/
noncomputable def keepLastDirectionP : Submodule ℝ PairM := keepPlaneP ⊓ annihP lastDirectionP

theorem mem_keepLP (X : PairM) : X ∈ keepLP ↔ ∃ R, SysExt.turnOf tenLine (SysExt.uFive R) = X := by
  rw [keepLP, SysExt.keepL_eq tenLine SysExt.tenLine_isTen, ← SysExt.range_uFive, ← LinearMap.range_comp]
  rfl

theorem pairTurn_injective : Function.Injective ((SysExt.turnOf tenLine).comp SysExt.uFive) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro R hR
  have h0 := SysExt.turnOf_eq_zero tenLine SysExt.tenLine_isTen (SysExt.uFive R) (SysExt.uFive_mem_skew R) hR
  exact SysExt.uFive_injective (by rw [h0, map_zero])

theorem vac_iff (R : Matrix (Fin 5) (Fin 5) ℝ) :
    SysExt.turnOf tenLine (SysExt.uFive R) *ᵥ vacP = 0 ↔ R.trace = 0 := by
  rw [← W_vacF, keep_vec_iff, SysExt.turn_vac_iff]

theorem plane_iff (R : Matrix (Fin 5) (Fin 5) ℝ) :
    SysExt.turnOf tenLine (SysExt.uFive R) * planeNP = planeNP * SysExt.turnOf tenLine (SysExt.uFive R) ↔
      ∀ s t, SysExt.crossP (s, t) → R s t = 0 := by
  rw [comm_transfer (W_turn (SysExt.uFive R)) (fun v => by rw [W_planeN]; rfl),
    SysExt.plane_comm_iff _ (SysExt.uFive_mem_skew R), SysExt.uFive_plane_iff]

theorem lastDirection_iff (R : Matrix (Fin 5) (Fin 5) ℝ) (htr : R.trace = 0)
    (hR : ∀ s t, SysExt.crossP (s, t) → R s t = 0) :
    SysExt.turnOf tenLine (SysExt.uFive R) *ᵥ lastDirectionP = 0 ↔ R 3 3 = 0 ∧ R 3 4 = 0 ∧ R 4 3 = 0 := by
  obtain ⟨c, hc, hP⟩ := lastDirectionP_eq
  rw [hP, Matrix.mulVec_smul, smul_eq_zero, or_iff_right hc, ← W_lastDirection, keep_vec_iff, SysExt.turn_lastDirection_iff R htr hR]

theorem keepVacP_eq :
    keepVacP = (LinearMap.ker (SysExt.kerP SysExt.singletP)).map ((SysExt.turnOf tenLine).comp SysExt.uFive) := by
  ext X
  rw [keepVacP, Submodule.mem_inf, mem_keepLP, mem_annihP, Submodule.mem_map]
  constructor
  · rintro ⟨⟨R, rfl⟩, hΩ⟩
    refine ⟨R, ?_, rfl⟩
    rw [SysExt.mem_ker_kerP]
    exact ⟨(vac_iff R).mp hΩ, fun _ h => h.elim⟩
  · rintro ⟨R, hR, rfl⟩
    rw [SysExt.mem_ker_kerP] at hR
    exact ⟨⟨R, rfl⟩, (vac_iff R).mpr hR.1⟩

theorem keepPlaneP_eq :
    keepPlaneP = (LinearMap.ker (SysExt.kerP SysExt.crossP)).map ((SysExt.turnOf tenLine).comp SysExt.uFive) := by
  ext X
  rw [keepPlaneP, Submodule.mem_inf, keepVacP_eq, Submodule.mem_map, Submodule.mem_map, SysExt.mem_commWith]
  constructor
  · rintro ⟨⟨R, hR, rfl⟩, hF⟩
    refine ⟨R, ?_, rfl⟩
    rw [SysExt.mem_ker_kerP] at hR ⊢
    exact ⟨hR.1, fun p hp => (plane_iff R).mp hF p.1 p.2 hp⟩
  · rintro ⟨R, hR, rfl⟩
    rw [SysExt.mem_ker_kerP] at hR
    exact ⟨⟨R, (SysExt.mem_ker_kerP _ R).mpr ⟨hR.1, fun _ h => h.elim⟩, rfl⟩,
      (plane_iff R).mpr fun s t h => hR.2 (s, t) h⟩

theorem keepLastDirectionP_eq :
    keepLastDirectionP = (LinearMap.ker (SysExt.kerP SysExt.lastDirectionP)).map ((SysExt.turnOf tenLine).comp SysExt.uFive) := by
  ext X
  rw [keepLastDirectionP, Submodule.mem_inf, keepPlaneP_eq, Submodule.mem_map, Submodule.mem_map, mem_annihP]
  constructor
  · rintro ⟨⟨R, hR, rfl⟩, hh⟩
    refine ⟨R, ?_, rfl⟩
    rw [SysExt.mem_ker_kerP] at hR ⊢
    have hc : ∀ s t, SysExt.crossP (s, t) → R s t = 0 := fun s t h => hR.2 (s, t) h
    obtain ⟨h1, h2, h3⟩ := (lastDirection_iff R hR.1 hc).mp hh
    refine ⟨hR.1, fun p hp => ?_⟩
    rcases hp with hp | rfl | rfl | rfl
    · exact hR.2 p hp
    · exact h1
    · exact h2
    · exact h3
  · rintro ⟨R, hR, rfl⟩
    rw [SysExt.mem_ker_kerP] at hR
    have hc : ∀ s t, SysExt.crossP (s, t) → R s t = 0 := fun s t h => hR.2 (s, t) (Or.inl h)
    refine ⟨⟨R, (SysExt.mem_ker_kerP _ R).mpr ⟨hR.1, fun p hp => hc p.1 p.2 hp⟩, rfl⟩, ?_⟩
    exact (lastDirection_iff R hR.1 hc).mpr
      ⟨hR.2 (3, 3) (Or.inr (Or.inl rfl)), hR.2 (3, 4) (Or.inr (Or.inr (Or.inl rfl))),
        hR.2 (4, 3) (Or.inr (Or.inr (Or.inr rfl)))⟩

/-- **The chain of the rotations of the pair, on `H ⊗ H ⊗ ℂ²`:** `so(10)` 45; keeping the comparison 25 (`u(5)`);
keeping also the singlet `Ω₊` 24 (`su(5)`); keeping also the plane count `N_F` 12 (`s(u(3) ⊕ u(2))`); keeping also the
last-step direction's two-spinor state `ℓ_h ⊗ e₊` 9 (`su(3) ⊕ u(1)`); at the plane `{3, 4}` with the last-step direction `3`. -/
theorem pair_chain :
    Module.finrank ℝ (SysExt.turnsTen tenLine) = 45 ∧ Module.finrank ℝ keepLP = 25 ∧
    Module.finrank ℝ keepVacP = 24 ∧ Module.finrank ℝ keepPlaneP = 12 ∧ Module.finrank ℝ keepLastDirectionP = 9 := by
  have e : ∀ S : Submodule ℝ (Matrix (Fin 5) (Fin 5) ℝ),
      Module.finrank ℝ (S.map ((SysExt.turnOf tenLine).comp SysExt.uFive)) = Module.finrank ℝ S := fun S =>
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ pairTurn_injective S)).symm
  refine ⟨SysExt.finrank_turnsTen tenLine SysExt.tenLine_isTen,
    SysExt.finrank_keepL tenLine SysExt.tenLine_isTen, ?_, ?_, ?_⟩
  · rw [keepVacP_eq, e, SysExt.finrank_su5]
  · rw [keepPlaneP_eq, e, SysExt.finrank_plane5]
  · rw [keepLastDirectionP_eq, e, SysExt.finrank_lastDirection5]

/-! ## Proposition 46 -/

/-- Proposition 46 at the plane `{3, 4}` with the last-step direction `3`; `PairWhole.lean`: `prop_46`, at every plane and with the centres. -/
theorem prop_46_plane34 :
    (∀ x y : SysExt.Ten, tenLine x * tenLine y + tenLine y * tenLine x = if x = y then (2 : ℂ) • 1 else 0) ∧
    Module.finrank ℝ (SysExt.turnsTen tenLine) = 45 ∧
    (-I) • ∑ t, tenLine (Sum.inl t) * tenLine (Sum.inr t) = (L - 1) ⊗ₖ σ₃ ∧
    (∀ k : Fin 16, Complex.exp (-(Real.pi / 4 : ℂ) * (Lvalue k : ℂ) * I) • rel k = (-I) • (swap *ᵥ rel k)) ∧
    Module.finrank ℝ keepLP = 25 ∧
    Module.finrank ℝ (SysExt.turnsTen tenLine ⊓ SysExt.commWith (L ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
      Submodule ℝ _) = 25 ∧
    SysExt.turnOf tenLine SysExt.cxJ = (1 / 2 : ℝ) • (I • ((L - 1) ⊗ₖ σ₃)) ∧
    vacP = kronVec Ω (Pi.single 0 1) ∧ Module.finrank ℝ keepVacP = 24 ∧
    planeNP = (1 / 2 : ℂ) • (1 - (γ 3 ⊗ₖ γ 3) ⊗ₖ σ₃) + (1 / 2 : ℂ) • (1 - (γ 4 ⊗ₖ γ 4) ⊗ₖ σ₃) ∧
    Module.finrank ℝ keepPlaneP = 12 ∧
    lastDirectionP = kronVec (ell 3) (Pi.single 0 1) ∧ Module.finrank ℝ keepLastDirectionP = 9 ∧
    (GroupsContinuumLaw.IsPlaneTurn GroupsContinuumLaw.Yc ∧ (∀ W, GroupsContinuumLaw.IsPlaneTurn W → GroupsContinuumLaw.Yc * W = W * GroupsContinuumLaw.Yc) ∧
      ∀ Z, GroupsContinuumLaw.IsPlaneTurn Z → (∀ W, GroupsContinuumLaw.IsPlaneTurn W → Z * W = W * Z) →
        ∃ a : ℝ, Z = (a : ℂ) • GroupsContinuumLaw.Yc) ∧
    (GroupsContinuumLaw.IsLastDirectionTurn GroupsContinuumLaw.Qc ∧ (∀ W, GroupsContinuumLaw.IsLastDirectionTurn W → GroupsContinuumLaw.Qc * W = W * GroupsContinuumLaw.Qc) ∧
      ∀ Z, GroupsContinuumLaw.IsLastDirectionTurn Z → (∀ W, GroupsContinuumLaw.IsLastDirectionTurn W → Z * W = W * Z) →
        ∃ a : ℝ, Z = (a : ℂ) • GroupsContinuumLaw.Qc) ∧
    Function.Surjective GroupsContinuumLaw.symHom ∧
    (∀ x, GroupsContinuumLaw.symHom x = 1 ↔ ∃ ζ : rootsOfUnity 6 ℂ, x = GroupsContinuumLaw.kerElt ζ) ∧
    Nat.card (rootsOfUnity 6 ℂ) = 6 ∧ IsCyclic (rootsOfUnity 6 ℂ) ∧
    (∑ S ∈ GroupsContinuumLaw.relSets, GroupsContinuumLaw.chargeZ GroupsContinuumLaw.y6 S = 0 ∧
      ∑ S ∈ GroupsContinuumLaw.relSets, GroupsContinuumLaw.chargeZ GroupsContinuumLaw.y6 S ^ 3 = 0) := by
  obtain ⟨c45, c25, c24, c12, c9⟩ := pair_chain
  refine ⟨tenLine_clifford, c45, comparison_as_turn, quarter_comparison, c25, SysExt.pair_keepL_finrank', ?_, rfl,
    c24, planeNP_eq, c12, rfl, c9, ⟨GroupsContinuumLaw.Yc_plane, GroupsContinuumLaw.Yc_central, GroupsContinuumLaw.plane_centre⟩,
    ⟨GroupsContinuumLaw.Qc_lastDirection, GroupsContinuumLaw.Qc_central, GroupsContinuumLaw.lastDirection_centre⟩, GroupsContinuumLaw.sym_surjective, GroupsContinuumLaw.sym_ker,
    GroupsContinuumLaw.ker_card, GroupsContinuumLaw.ker_cyclic, ⟨GroupsContinuumLaw.trY, GroupsContinuumLaw.trY3⟩⟩
  rw [SysExt.turnOf_cxJ tenLine SysExt.tenLine_isTen, SysExt.pairSum_tenLine]

end Comparison.System.Existence
