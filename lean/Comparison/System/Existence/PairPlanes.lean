import Comparison.System.Existence.PairModel

/-!
# The proof system, the existence layer: Prop. 46 at every plane

A relabelling `π` of the five directions acts on `Λℂ⁵` by `Λ(P_π)` (`relabel`); it carries
`ε_t, ι_t` to `ε_{πt}, ι_{πt}` (`relabel_εx`, `relabel_ιx`), the ten lines to the ten lines, every rotation to a rotation, the
comparison to itself, `N_a + N_b` to `N_{πa} + N_{πb}` and `f_{T_a}` to `±f_{T_{πa}}`. So the chain at the plane
`{3, 4}` (`SysExt.turns_chain`) is the chain at every plane, and `W` carries it to the pair (`pair_chain_plane`).
-/

namespace Comparison.System.Existence

open Matrix Complex Kronecker

/-! ## The relabelling of the five directions on `Λℂ⁵` -/

/-- The permutation matrix of `π`: `O e_b = e_{π b}`. -/
def permO (π : Equiv.Perm (Fin 5)) : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun a b => if a = π b then 1 else 0

theorem permO_col (π : Equiv.Perm (Fin 5)) (b : Fin 5) : (permO π).col b = Pi.single (π b) 1 := by
  funext a
  simp [permO, Matrix.col_apply, Pi.single_apply]

theorem perm_inv_apply_self (π : Equiv.Perm (Fin 5)) (x : Fin 5) : π⁻¹ (π x) = x := π.symm_apply_apply x

theorem perm_apply_inv_self (π : Equiv.Perm (Fin 5)) (x : Fin 5) : π (π⁻¹ x) = x := π.apply_symm_apply x

theorem permO_transpose (π : Equiv.Perm (Fin 5)) : (permO π)ᵀ = permO π⁻¹ := by
  ext a b
  simp only [Matrix.transpose_apply, permO, Matrix.of_apply]
  by_cases h : b = π a
  · rw [if_pos h, if_pos]
    rw [h, perm_inv_apply_self]
  · rw [if_neg h, if_neg]
    intro e
    apply h
    rw [e, perm_apply_inv_self]

theorem permO_orth (π : Equiv.Perm (Fin 5)) : (permO π)ᵀ * permO π = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (π a)]
  · simp [permO, Matrix.one_apply]
  · intro c _ hc
    simp [permO, hc]
  · simp

/-- **The relabelling of the five directions on `Λℂ⁵`**, `Λ(P_π)`. -/
noncomputable abbrev relabel (π : Equiv.Perm (Fin 5)) : SysExt.FockE := SysExt.extMap (permO π)

theorem relabel_εx (π : Equiv.Perm (Fin 5)) (a : Fin 5) :
    relabel π * SysExt.εx a = SysExt.εx (π a) * relabel π := by
  rw [relabel, SysExt.extMap_εx, SysExt.colStep, permO_col, SysExt.εv_single]

theorem relabel_ιx (π : Equiv.Perm (Fin 5)) (a : Fin 5) :
    relabel π * SysExt.ιx a = SysExt.ιx (π a) * relabel π := by
  rw [relabel, SysExt.extMap_ιx _ (permO_orth π), permO_col, SysExt.ιv_single]

theorem relabel_inv (π : Equiv.Perm (Fin 5)) :
    relabel π * relabel π⁻¹ = 1 ∧ relabel π⁻¹ * relabel π = 1 := by
  have := SysExt.extMap_mul_transpose (permO π) (permO_orth π)
  rw [permO_transpose] at this
  exact this

theorem relabel_vac (π : Equiv.Perm (Fin 5)) : relabel π SysExt.vacF = SysExt.vacF :=
  SysExt.extMap_vac _

theorem relabel_inl (π : Equiv.Perm (Fin 5)) (a : Fin 5) :
    relabel π * SysExt.fockLine (Sum.inl a) = SysExt.fockLine (Sum.inl (π a)) * relabel π := by
  simp only [SysExt.fockLine, mul_add, add_mul, relabel_εx, relabel_ιx]

theorem relabel_inr (π : Equiv.Perm (Fin 5)) (a : Fin 5) :
    relabel π * SysExt.fockLine (Sum.inr a) = SysExt.fockLine (Sum.inr (π a)) * relabel π := by
  simp only [SysExt.fockLine, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, relabel_εx, relabel_ιx]

/-- The relabelling of the ten lines. -/
def tenPerm (π : Equiv.Perm (Fin 5)) : Equiv.Perm SysExt.Ten := Equiv.sumCongr π π

theorem relabel_line (π : Equiv.Perm (Fin 5)) (x : SysExt.Ten) :
    relabel π * SysExt.fockLine x = SysExt.fockLine (tenPerm π x) * relabel π := by
  rcases x with a | a
  · exact relabel_inl π a
  · exact relabel_inr π a

theorem relabel_turn (π : Equiv.Perm (Fin 5)) (M : Matrix SysExt.Ten SysExt.Ten ℝ) :
    relabel π * SysExt.turnOf SysExt.fockLine M =
      SysExt.turnOf SysExt.fockLine (M.submatrix (tenPerm π).symm (tenPerm π).symm) * relabel π := by
  have hP : ∀ x y, relabel π * (SysExt.fockLine x * SysExt.fockLine y) =
      SysExt.fockLine (tenPerm π x) * SysExt.fockLine (tenPerm π y) * relabel π := by
    intro x y
    rw [← mul_assoc, relabel_line, mul_assoc, relabel_line, ← mul_assoc]
  rw [SysExt.turnOf_apply, SysExt.turnOf_apply, Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (tenPerm π) _ _ fun x => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (tenPerm π) _ _ fun y => ?_
  rw [mul_smul_comm, hP, smul_mul_assoc, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

theorem relabel_pairSum (π : Equiv.Perm (Fin 5)) :
    relabel π * SysExt.pairSum SysExt.fockLine = SysExt.pairSum SysExt.fockLine * relabel π := by
  rw [SysExt.pairSum, Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv π _ _ fun t => ?_
  rw [← mul_assoc, relabel_inl, mul_assoc, relabel_inr, ← mul_assoc]

/-- The plane count of `{a, b}` on `Λℂ⁵`. -/
noncomputable def planeNF (a b : Fin 5) : SysExt.FockE := SysExt.εx a * SysExt.ιx a + SysExt.εx b * SysExt.ιx b

theorem relabel_planeNF (π : Equiv.Perm (Fin 5)) (a b : Fin 5) :
    relabel π * planeNF a b = planeNF (π a) (π b) * relabel π := by
  have h1 : ∀ c : Fin 5, relabel π * (SysExt.εx c * SysExt.ιx c) =
      SysExt.εx (π c) * SysExt.ιx (π c) * relabel π := by
    intro c
    rw [← mul_assoc, relabel_εx, mul_assoc, relabel_ιx, ← mul_assoc]
  simp only [planeNF, mul_add, add_mul, h1]

/-- The ordered `ε`-word over `S` with the lines relabelled is `±f_{π(S)}`. -/
theorem relabel_word (π : Equiv.Perm (Fin 5)) (S : Finset (Fin 5)) :
    ∃ c : ℂ, (c = 1 ∨ c = -1) ∧
      SysExt.ordProd (fun a => (SysExt.εx (π a) : SysExt.FockE)) S (Pi.single (∅ : Finset (Fin 5)) (1 : ℂ)) =
        c • (Pi.single (S.image π) (1 : ℂ) : Finset (Fin 5) → ℂ) := by
  induction S using Finset.induction_on_min with
  | empty => exact ⟨1, Or.inl rfl, by simp⟩
  | insert m S hm ih =>
    obtain ⟨c, hc, h⟩ := ih
    have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
    have hπ : π m ∉ S.image π := by
      rw [Finset.mem_image]
      rintro ⟨y, hy, e⟩
      exact hmS (π.injective e ▸ hy)
    refine ⟨c * SysExt.extSign (R := ℂ) (π m) (S.image π), ?_, ?_⟩
    · rw [SysExt.extSign_eq]
      rcases neg_one_pow_eq_or ℂ ((S.image π).filter (· < π m)).card with e | e <;> rw [e] <;>
        rcases hc with hc | hc <;> rw [hc] <;> norm_num
    · rw [SysExt.ordProd_insert_min _ hm, Module.End.mul_apply, h, map_smul, SysExt.εx_single, if_neg hπ,
        smul_smul, Finset.image_insert]

theorem relabel_single (π : Equiv.Perm (Fin 5)) (S : Finset (Fin 5)) :
    ∃ c : ℂ, c ≠ 0 ∧ relabel π (Pi.single S (1 : ℂ)) = c • (Pi.single (S.image π) (1 : ℂ) : Finset (Fin 5) → ℂ) := by
  obtain ⟨c, hc, h⟩ := relabel_word π S
  refine ⟨c, by rcases hc with hc | hc <;> rw [hc] <;> norm_num, ?_⟩
  rw [relabel, SysExt.extMap_single, ← h]
  congr 1
  exact SysExt.ordProd_congr fun a _ => by rw [SysExt.colStep, permO_col, SysExt.εv_single]

theorem image_erase_univ (π : Equiv.Perm (Fin 5)) (a : Fin 5) :
    (Finset.univ.erase a).image π = Finset.univ.erase (π a) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact fun e => hy (π.injective e)
  · intro hx
    exact ⟨π⁻¹ x, fun e => hx (by rw [← e, perm_apply_inv_self]), perm_apply_inv_self π x⟩

/-! ## The chain on `Λℂ⁵` at every plane -/

/-- The rotations on `Λℂ⁵` that keep the comparison, the singlet and the plane count of `{a, b}`. -/
noncomputable def keepPlaneF' (a b : Fin 5) : Submodule ℝ SysExt.FockE :=
  SysExt.keepVacF ⊓ SysExt.commWith (planeNF a b)

/-- … and also the last-step direction's two-spinor state `f_{T_a}`. -/
noncomputable def keepLastDirectionF' (a b : Fin 5) : Submodule ℝ SysExt.FockE :=
  keepPlaneF' a b ⊓ SysExt.annih (Pi.single (Finset.univ.erase a) 1)

/-- Conjugation by the relabelling. -/
noncomputable def conjE (π : Equiv.Perm (Fin 5)) : SysExt.FockE ≃ₗ[ℝ] SysExt.FockE where
  toFun X := relabel π * X * relabel π⁻¹
  invFun X := relabel π⁻¹ * X * relabel π
  map_add' X Y := by simp only [mul_add, add_mul]
  map_smul' c X := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]
  left_inv X := by
    obtain ⟨h1, h2⟩ := relabel_inv π
    change relabel π⁻¹ * (relabel π * X * relabel π⁻¹) * relabel π = X
    rw [show relabel π⁻¹ * (relabel π * X * relabel π⁻¹) * relabel π =
      (relabel π⁻¹ * relabel π) * X * (relabel π⁻¹ * relabel π) by noncomm_ring, h2, one_mul, mul_one]
  right_inv X := by
    obtain ⟨h1, h2⟩ := relabel_inv π
    change relabel π * (relabel π⁻¹ * X * relabel π) * relabel π⁻¹ = X
    rw [show relabel π * (relabel π⁻¹ * X * relabel π) * relabel π⁻¹ =
      (relabel π * relabel π⁻¹) * X * (relabel π * relabel π⁻¹) by noncomm_ring, h1, one_mul, mul_one]

theorem conjE_apply (π : Equiv.Perm (Fin 5)) (X : SysExt.FockE) :
    conjE π X = relabel π * X * relabel π⁻¹ := rfl

theorem conj_of_comm (π : Equiv.Perm (Fin 5)) {C C' : SysExt.FockE} (hC : relabel π * C = C' * relabel π)
    {X : SysExt.FockE} (hX : X * C = C * X) : conjE π X * C' = C' * conjE π X := by
  obtain ⟨h1, h2⟩ := relabel_inv π
  have hC' : C' = relabel π * C * relabel π⁻¹ := by
    rw [hC, mul_assoc, h1, mul_one]
  rw [conjE_apply, hC']
  rw [show relabel π * X * relabel π⁻¹ * (relabel π * C * relabel π⁻¹) =
    relabel π * X * (relabel π⁻¹ * relabel π) * C * relabel π⁻¹ by noncomm_ring, h2, mul_one,
    show relabel π * C * relabel π⁻¹ * (relabel π * X * relabel π⁻¹) =
    relabel π * C * (relabel π⁻¹ * relabel π) * X * relabel π⁻¹ by noncomm_ring, h2, mul_one,
    mul_assoc (relabel π) X C, hX, ← mul_assoc]

theorem conj_turn_mem (π : Equiv.Perm (Fin 5)) {X : SysExt.FockE} (hX : X ∈ SysExt.turnsTen SysExt.fockLine) :
    conjE π X ∈ SysExt.turnsTen SysExt.fockLine := by
  obtain ⟨M, hM, rfl⟩ := hX
  obtain ⟨h1, h2⟩ := relabel_inv π
  refine ⟨M.submatrix (tenPerm π).symm (tenPerm π).symm, ?_, ?_⟩
  · change (M.submatrix _ _)ᵀ = -(M.submatrix _ _)
    rw [Matrix.transpose_submatrix]
    have hM' : Mᵀ = -M := hM
    rw [hM']
    rfl
  · change SysExt.turnOf SysExt.fockLine _ = relabel π * SysExt.turnOf SysExt.fockLine M * relabel π⁻¹
    rw [relabel_turn, mul_assoc, h1, mul_one]

theorem conj_vac (π : Equiv.Perm (Fin 5)) {X : SysExt.FockE} (hX : X SysExt.vacF = 0) :
    conjE π X SysExt.vacF = 0 := by
  rw [conjE_apply, Module.End.mul_apply, Module.End.mul_apply, relabel_vac, hX, map_zero]

/-- **The relabelling carries the rotations that keep the plane `{a, b}` to those that keep `{πa, πb}`.** -/
theorem conj_keepPlane (π : Equiv.Perm (Fin 5)) (a b : Fin 5) {X : SysExt.FockE} (hX : X ∈ keepPlaneF' a b) :
    conjE π X ∈ keepPlaneF' (π a) (π b) := by
  obtain ⟨⟨⟨hT, hL⟩, hV⟩, hF⟩ := hX
  exact ⟨⟨⟨conj_turn_mem π hT, conj_of_comm π (relabel_pairSum π) hL⟩, conj_vac π hV⟩,
    conj_of_comm π (relabel_planeNF π a b) hF⟩

theorem conj_keepLastDirection (π : Equiv.Perm (Fin 5)) (a b : Fin 5) {X : SysExt.FockE} (hX : X ∈ keepLastDirectionF' a b) :
    conjE π X ∈ keepLastDirectionF' (π a) (π b) := by
  obtain ⟨hF, hH⟩ := hX
  refine ⟨conj_keepPlane π a b hF, ?_⟩
  change (relabel π * X * relabel π⁻¹) (Pi.single (Finset.univ.erase (π a)) (1 : ℂ)) = 0
  have hH' : X (Pi.single (Finset.univ.erase a) (1 : ℂ)) = 0 := hH
  obtain ⟨c, -, hc⟩ := relabel_single π⁻¹ (Finset.univ.erase (π a))
  rw [image_erase_univ, perm_inv_apply_self] at hc
  rw [Module.End.mul_apply, Module.End.mul_apply, hc, map_smul, hH', smul_zero, map_zero]

theorem keepPlane_map (π : Equiv.Perm (Fin 5)) (a b : Fin 5) :
    keepPlaneF' (π a) (π b) = (keepPlaneF' a b).map (conjE π).toLinearMap := by
  ext Y
  constructor
  · intro hY
    refine ⟨conjE π⁻¹ Y, ?_, ?_⟩
    · have := conj_keepPlane π⁻¹ (π a) (π b) hY
      rwa [perm_inv_apply_self, perm_inv_apply_self] at this
    · change conjE π (conjE π⁻¹ Y) = Y
      have e : ∀ Z, conjE π⁻¹ Z = (conjE π).symm Z := by
        intro Z
        change relabel π⁻¹ * Z * relabel π⁻¹⁻¹ = relabel π⁻¹ * Z * relabel π
        rw [inv_inv]
      rw [e, LinearEquiv.apply_symm_apply]
  · rintro ⟨X, hX, rfl⟩
    exact conj_keepPlane π a b hX

theorem keepLastDirection_map (π : Equiv.Perm (Fin 5)) (a b : Fin 5) :
    keepLastDirectionF' (π a) (π b) = (keepLastDirectionF' a b).map (conjE π).toLinearMap := by
  ext Y
  constructor
  · intro hY
    refine ⟨conjE π⁻¹ Y, ?_, ?_⟩
    · have := conj_keepLastDirection π⁻¹ (π a) (π b) hY
      rwa [perm_inv_apply_self, perm_inv_apply_self] at this
    · change conjE π (conjE π⁻¹ Y) = Y
      have e : ∀ Z, conjE π⁻¹ Z = (conjE π).symm Z := by
        intro Z
        change relabel π⁻¹ * Z * relabel π⁻¹⁻¹ = relabel π⁻¹ * Z * relabel π
        rw [inv_inv]
      rw [e, LinearEquiv.apply_symm_apply]
  · rintro ⟨X, hX, rfl⟩
    exact conj_keepLastDirection π a b hX

theorem perm_to_plane : ∀ h k : Fin 5, h ≠ k →
    ((Equiv.swap 3 h).trans (Equiv.swap (Equiv.swap 3 h 4) k)) 3 = h ∧
    ((Equiv.swap 3 h).trans (Equiv.swap (Equiv.swap 3 h 4) k)) 4 = k := by
  decide +kernel

theorem keepPlane34 : keepPlaneF' 3 4 = SysExt.keepPlaneF := rfl

theorem keepLastDirection34 : keepLastDirectionF' 3 4 = SysExt.keepLastDirectionF := by
  have e : (Finset.univ.erase (3 : Fin 5)) = {0, 1, 2, 4} := by decide
  rw [keepLastDirectionF', e]
  rfl

/-- **On `Λℂ⁵` at every plane `{h, k}`:** the rotations keeping the comparison, the singlet and `N_h + N_k` have dimension
12, keeping also `f_{T_h}` 9. -/
theorem fock_chain_plane (h k : Fin 5) (hk : h ≠ k) :
    Module.finrank ℝ (keepPlaneF' h k) = 12 ∧ Module.finrank ℝ (keepLastDirectionF' h k) = 9 := by
  obtain ⟨-, -, -, c12, c9⟩ := SysExt.turns_chain
  obtain ⟨e3, e4⟩ := perm_to_plane h k hk
  set π := (Equiv.swap 3 h).trans (Equiv.swap (Equiv.swap 3 h 4) k)
  refine ⟨?_, ?_⟩
  · rw [← e3, ← e4, keepPlane_map, LinearEquiv.finrank_map_eq, keepPlane34, c12]
  · rw [← e3, ← e4, keepLastDirection_map, LinearEquiv.finrank_map_eq, keepLastDirection34, c9]

/-! ## The pair at every plane -/

theorem W_planeNF (a b : Fin 5) (v : Finset (Fin 5) → ℂ) :
    Wmap (planeNF a b v) = (crP a * anP a + crP b * anP b) *ᵥ Wmap v := by
  simp only [planeNF, LinearMap.add_apply, Module.End.mul_apply, map_add, W_εx, W_ιx, Matrix.add_mulVec,
    Matrix.mulVec_mulVec]

theorem W_pairSum (v : Finset (Fin 5) → ℂ) :
    Wmap (SysExt.pairSum SysExt.fockLine v) = SysExt.pairSum tenLine *ᵥ Wmap v := by
  simp only [SysExt.pairSum, LinearMap.sum_apply, Module.End.mul_apply, map_sum, W_line, Matrix.sum_mulVec,
    Matrix.mulVec_mulVec]

theorem gamma_kron_ell_gen (a t : Fin 5) : (γ t ⊗ₖ γ t) *ᵥ ell a = if t = a then ell a else -ell a := by
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

/-- The last-step direction's two-spinor state of the pair at the last-step direction `a`, `ℓ_a ⊗ e₊`. -/
noncomputable def lastDirectionAtP (a : Fin 5) : PairV := kronVec (ell a) (Pi.single 0 1)

theorem numP_lastDirectionAtP (a t : Fin 5) :
    (crP t * anP t) *ᵥ lastDirectionAtP a = (if t ∈ Finset.univ.erase a then (1 : ℂ) else 0) • lastDirectionAtP a := by
  rw [numP_eq, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, lastDirectionAtP, kronVec_e₀_σ₃, gamma_kron_ell_gen]
  by_cases ht : t = a
  · have : t ∉ Finset.univ.erase a := by simp [ht]
    rw [if_pos ht, if_neg this, sub_self, smul_zero, zero_smul]
  · have : t ∈ Finset.univ.erase a := by simp [ht]
    rw [if_neg ht, if_pos this, one_smul]
    funext q
    simp only [kronVec, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    ring

theorem lastDirectionAtP_ne (a : Fin 5) : lastDirectionAtP a ≠ 0 := by
  intro h
  have h1 : ∀ p : Two, lastDirectionAtP a (p, 0) = ell a p := by
    intro p
    simp [lastDirectionAtP, kronVec]
  have hl : ell a = 0 := by
    funext p
    rw [← h1 p, h]
    rfl
  have hn := rel_inner (lineIdx a) (lineIdx a)
  rw [← ell_eq_rel a, hl] at hn
  simp at hn

theorem lastDirectionAtP_eq (a : Fin 5) : ∃ c : ℂ, c ≠ 0 ∧ lastDirectionAtP a = c • wS (Finset.univ.erase a) := by
  obtain ⟨c, hc⟩ := joint_eigen (Finset.univ.erase a) (lastDirectionAtP a) (numP_lastDirectionAtP a)
  exact ⟨c, fun h0 => lastDirectionAtP_ne a (by rw [hc, h0, zero_smul]), hc⟩

/-- The rotations of the pair that keep the comparison, the singlet and the plane count of `{a, b}`. -/
noncomputable def keepPlaneP' (a b : Fin 5) : Submodule ℝ PairM :=
  keepVacP ⊓ SysExt.commWith (crP a * anP a + crP b * anP b)

/-- … and also the last-step direction's two-spinor state `ℓ_a ⊗ e₊`. -/
noncomputable def keepLastDirectionP' (a b : Fin 5) : Submodule ℝ PairM := keepPlaneP' a b ⊓ annihP (lastDirectionAtP a)

theorem transfer_plane (a b : Fin 5) (M : Matrix SysExt.Ten SysExt.Ten ℝ) (hM : Mᵀ = -M) :
    SysExt.turnOf tenLine M ∈ keepPlaneP' a b ↔ SysExt.turnOf SysExt.fockLine M ∈ keepPlaneF' a b := by
  have hT : SysExt.turnOf tenLine M ∈ SysExt.turnsTen tenLine := ⟨M, hM, rfl⟩
  have hTF : SysExt.turnOf SysExt.fockLine M ∈ SysExt.turnsTen SysExt.fockLine := ⟨M, hM, rfl⟩
  have hL := comm_transfer (W_turn M) W_pairSum
  have hF := comm_transfer (W_turn M) (W_planeNF a b)
  have hV : SysExt.turnOf tenLine M *ᵥ vacP = 0 ↔ SysExt.turnOf SysExt.fockLine M SysExt.vacF = 0 := by
    rw [← W_vacF, keep_vec_iff]
  simp only [keepPlaneP', keepPlaneF', keepVacP, SysExt.keepVacF, keepLP, SysExt.keepLF, Submodule.mem_inf,
    SysExt.mem_commWith, mem_annihP, SysExt.mem_annih]
  rw [hL, hF, hV]
  exact ⟨fun h => ⟨⟨⟨hTF, h.1.1.2⟩, h.1.2⟩, h.2⟩, fun h => ⟨⟨⟨hT, h.1.1.2⟩, h.1.2⟩, h.2⟩⟩

theorem transfer_lastDirection (a b : Fin 5) (M : Matrix SysExt.Ten SysExt.Ten ℝ) (hM : Mᵀ = -M) :
    SysExt.turnOf tenLine M ∈ keepLastDirectionP' a b ↔ SysExt.turnOf SysExt.fockLine M ∈ keepLastDirectionF' a b := by
  have hH : SysExt.turnOf tenLine M *ᵥ lastDirectionAtP a = 0 ↔
      SysExt.turnOf SysExt.fockLine M (Pi.single (Finset.univ.erase a) 1) = 0 := by
    obtain ⟨c, hc, hP⟩ := lastDirectionAtP_eq a
    rw [hP, Matrix.mulVec_smul, smul_eq_zero, or_iff_right hc, ← Wmap_single, keep_vec_iff]
  simp only [keepLastDirectionP', keepLastDirectionF', Submodule.mem_inf, mem_annihP, SysExt.mem_annih]
  rw [transfer_plane a b M hM, hH]

/-- Two subspaces of rotations with the same skew matrices have the same dimension. -/
theorem finrank_transfer (KP : Submodule ℝ PairM) (KF : Submodule ℝ SysExt.FockE)
    (hP : KP ≤ SysExt.turnsTen tenLine) (hF : KF ≤ SysExt.turnsTen SysExt.fockLine)
    (h : ∀ M : Matrix SysExt.Ten SysExt.Ten ℝ, Mᵀ = -M →
      (SysExt.turnOf tenLine M ∈ KP ↔ SysExt.turnOf SysExt.fockLine M ∈ KF)) :
    Module.finrank ℝ KP = Module.finrank ℝ KF := by
  set fP := (SysExt.turnOf tenLine).comp SysExt.skewTen.subtype
  set fF := (SysExt.turnOf SysExt.fockLine).comp SysExt.skewTen.subtype
  have injP : Function.Injective fP := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    exact Subtype.ext (SysExt.turnOf_eq_zero tenLine SysExt.tenLine_isTen m.1 m.2 hm)
  have injF : Function.Injective fF := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    exact Subtype.ext (SysExt.turnOf_eq_zero SysExt.fockLine SysExt.fockLine_isTen m.1 m.2 hm)
  have rP : KP ≤ LinearMap.range fP := by
    intro X hX
    obtain ⟨M, hM, rfl⟩ := hP hX
    exact ⟨⟨M, hM⟩, rfl⟩
  have rF : KF ≤ LinearMap.range fF := by
    intro X hX
    obtain ⟨M, hM, rfl⟩ := hF hX
    exact ⟨⟨M, hM⟩, rfl⟩
  have hc : KP.comap fP = KF.comap fF := by
    ext m
    exact h m.1 m.2
  rw [← Submodule.map_comap_eq_self rP, ← Submodule.map_comap_eq_self rF, hc,
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective fP injP _).symm,
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective fF injF _).symm]

theorem keepPlaneP'_le (a b : Fin 5) : keepPlaneP' a b ≤ SysExt.turnsTen tenLine :=
  fun _ hX => hX.1.1.1

theorem keepPlaneF'_le (a b : Fin 5) : keepPlaneF' a b ≤ SysExt.turnsTen SysExt.fockLine :=
  fun _ hX => hX.1.1.1

/-- **The chain of the rotations of the pair at every plane `{h, k}`:** keeping the comparison, the singlet and the plane count
`N_F = c_ha_h + c_ka_k`: 12; keeping also the last-step direction's two-spinor state `ℓ_h ⊗ e₊`: 9. -/
theorem pair_chain_plane (h k : Fin 5) (hk : h ≠ k) :
    Module.finrank ℝ (keepPlaneP' h k) = 12 ∧ Module.finrank ℝ (keepLastDirectionP' h k) = 9 := by
  obtain ⟨f12, f9⟩ := fock_chain_plane h k hk
  refine ⟨?_, ?_⟩
  · rw [finrank_transfer _ _ (keepPlaneP'_le h k) (keepPlaneF'_le h k) (transfer_plane h k), f12]
  · rw [finrank_transfer (keepLastDirectionP' h k) (keepLastDirectionF' h k) (fun X hX => keepPlaneP'_le h k hX.1)
      (fun X hX => keepPlaneF'_le h k hX.1) (transfer_lastDirection h k), f9]

/-- **Proposition 46 at every plane:** with `N_F = Σ_{t ∈ F}(1 − (γ_t ⊗ γ_t) ⊗ σ_z)/2` and the last-step direction's two-spinor state
`ℓ_h ⊗ e₊`, the rotations of the pair that keep the comparison, the singlet, `N_F` and `ℓ_h ⊗ e₊` have dimensions 12 and 9
for every plane `F = {h, k}`. -/
theorem prop_46_every_plane (h k : Fin 5) (hk : h ≠ k) :
    crP h * anP h + crP k * anP k =
      (1 / 2 : ℂ) • (1 - (γ h ⊗ₖ γ h) ⊗ₖ σ₃) + (1 / 2 : ℂ) • (1 - (γ k ⊗ₖ γ k) ⊗ₖ σ₃) ∧
    lastDirectionAtP h = kronVec (ell h) (Pi.single 0 1) ∧
    Module.finrank ℝ (keepPlaneP' h k) = 12 ∧ Module.finrank ℝ (keepLastDirectionP' h k) = 9 := by
  obtain ⟨f12, f9⟩ := pair_chain_plane h k hk
  exact ⟨by rw [numP_eq, numP_eq], rfl, f12, f9⟩

/-- Proposition 46, the chain of the rotations of the pair (`PairWhole.lean`: `prop_46`, with the centres). The ten lines of a pair on `H ⊗ H ⊗ ℂ²`,
`Γ_a = γ_a ⊗ 1 ⊗ σ_x`, `Γ_{5+a} = 1 ⊗ γ_a ⊗ σ_y`, anticommute, `Γ_xΓ_y + Γ_yΓ_x = 2δ_xy`; their rotations `½Γ_xΓ_y` span
`so(10)`, dimension 45; `−i Σ_t Γ_tΓ_{5+t} = (L − 1) ⊗ σ_z`, `L − 1` on the two-spinor states (`σ_z = +1`), and
`e^{−iπL/4} = −iP` on each two-spinor state; the rotations keeping the comparison are `u(5)`, 25 (keeping `L ⊗ 1` likewise), with
centre the complex structure `ρ(J) = ½ i(L − 1) ⊗ σ_z`; keeping also the singlet `Ω ⊗ e₊`: `su(5)`, 24; keeping also the
plane count `N_F = Σ_{t ∈ F} (1 − (γ_t ⊗ γ_t) ⊗ σ_z)/2`: `s(u(3) ⊕ u(2))`, 12; keeping also the last-step direction's two-spinor state
`ℓ_h ⊗ e₊`: `su(3) ⊕ u(1)`, 9 — at every plane `F = {h, k}` with the last-step direction `h`; the centres, as `5 × 5` rotations of
`ℂ⁵ = C ⊕ F`, are `ℝ·iY` and `ℝ·iQ`; `(A, B, z) ↦ (z²A, z̄³B)` maps `SU(3) × SU(2) × U(1)` onto `S(U(3) × U(2))` with
kernel the six images of the sixth roots of unity, cyclic of order six; and `Tr Y = Tr Y³ = 0` on the sixteen.

Recognition: the gauge group of the standard model, `S(U(2) × U(3)) = (SU(3) × SU(2) × U(1))/ℤ₆`, twelve
generators, held by `SU(5)`. Uses Props. 4, 10, 11, 21, 45. -/
theorem prop_46_chain :
    ((∀ x y : SysExt.Ten, tenLine x * tenLine y + tenLine y * tenLine x = if x = y then (2 : ℂ) • 1 else 0) ∧
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
      ∑ S ∈ GroupsContinuumLaw.relSets, GroupsContinuumLaw.chargeZ GroupsContinuumLaw.y6 S ^ 3 = 0)) ∧
    (∀ h k : Fin 5, h ≠ k →
      crP h * anP h + crP k * anP k =
        (1 / 2 : ℂ) • (1 - (γ h ⊗ₖ γ h) ⊗ₖ σ₃) + (1 / 2 : ℂ) • (1 - (γ k ⊗ₖ γ k) ⊗ₖ σ₃) ∧
      lastDirectionAtP h = kronVec (ell h) (Pi.single 0 1) ∧
      Module.finrank ℝ (keepPlaneP' h k) = 12 ∧ Module.finrank ℝ (keepLastDirectionP' h k) = 9) :=
  ⟨prop_46_plane34, fun h k hk => prop_46_every_plane h k hk⟩

end Comparison.System.Existence
