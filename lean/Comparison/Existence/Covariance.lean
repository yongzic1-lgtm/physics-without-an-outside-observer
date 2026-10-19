module

public import Comparison.Existence.Spin

/-!
# Book VII. The vertical step is covariant under every rotation (Proposition 33)

On the exterior algebra of `n`
directions (`Exterior.lean`): coefficient functions `Finset (Fin n) → R`, the basis `f_S = Pi.single S 1`.

* `ordProd E S`: the ordered product `E_{s₁} E_{s₂} ⋯ E_{s_r}` over `S = {s₁ < ⋯ < s_r}`.
  `ordProd_mul_left`: for any family with `E_aE_b = −E_bE_a` (`a ≠ b`) and `E_a² = z_a` central,
  `E_a · E_S = (−1)^{#{c ∈ S : c < a}} · (z_a E_{S∖{a}} or E_{S ∪ {a}})`. It serves the
  exterior algebra (`z = 0`), the vertical steps (`z = 1`) and the Clifford algebra alike.
* `ordProd_εx_vac`, `ordProd_Jx_vac`: **`J_{s₁} ⋯ J_{s_r} f_∅ = f_S`** (and the same with `ε`).
* `εv`, `ιv`, `Jv`: the steps along a vector, `ε(v) = Σ_a v_a ε_a`; `εv_mul_self`, `εv_anticomm`,
  `ιv_εv_add`: `ι(v)ε(w) + ε(w)ι(v) = ⟨v, w⟩`; `Jv_anticomm`: `J(v)J(w) + J(w)J(v) = 2⟨v, w⟩`.
* `extMap O`, written `Λ(O)`: `Λ(O) f_S = Oe_{s₁} ∧ ⋯ ∧ Oe_{s_r}` (`extMap_single`).
  `extMap_εx`: **`Λ(O) ε_a = ε(Oe_a) Λ(O)`** for every matrix `O`; `extMap_mul`: `Λ(OP) = Λ(O)Λ(P)`;
  `extMap_one`; `extMap_ιx`: `Λ(O) ι_a = ι(Oe_a) Λ(O)` for orthogonal `O`.
* `extMap_conj_Jv`: **`Λ(O) J(v) Λ(O)⁻¹ = J(Ov)`** for every orthogonal `O`, with
  `Λ(O)⁻¹ = Λ(Oᵀ)` (`extMap_mul_transpose`); `extUnits`: `O ↦ Λ(O)` is a homomorphism from the
  orthogonal group into the invertible operators, and `extUnits_conj_Jv` states the covariance with
  the inverse.
-/

@[expose] public section

namespace Comparison

open Finset
open scoped Matrix

/-! ## Ordered products -/

section Ordered

variable {A : Type*} {n : ℕ}

/-- **The ordered product** `E_{s₁} E_{s₂} ⋯ E_{s_r}` over `S = {s₁ < s₂ < ⋯ < s_r}`. -/
def ordProd [Monoid A] (E : Fin n → A) (S : Finset (Fin n)) : A :=
  ((S.sort (· ≤ ·)).map E).prod

@[simp]
theorem ordProd_empty [Monoid A] (E : Fin n → A) : ordProd E ∅ = 1 := by
  simp [ordProd]

theorem ordProd_singleton [Monoid A] (E : Fin n → A) (a : Fin n) : ordProd E {a} = E a := by
  simp [ordProd]

/-- Putting a direction below all the others in front. -/
theorem ordProd_insert_min [Monoid A] (E : Fin n → A) {a : Fin n} {S : Finset (Fin n)}
    (h : ∀ x ∈ S, a < x) : ordProd E (insert a S) = E a * ordProd E S := by
  have ha : a ∉ S := fun h' => lt_irrefl a (h a h')
  unfold ordProd
  rw [Finset.sort_insert (· ≤ ·) (fun b hb => (h b hb).le) ha, List.map_cons, List.prod_cons]

theorem ordProd_congr [Monoid A] {E E' : Fin n → A} {S : Finset (Fin n)}
    (h : ∀ x ∈ S, E x = E' x) : ordProd E S = ordProd E' S := by
  unfold ordProd
  congr 1
  exact List.map_congr_left fun x hx => h x ((Finset.mem_sort _).mp hx)

/-- An element that intertwines each factor intertwines the ordered product. -/
theorem ordProd_intertwine [Monoid A] (E E' : Fin n → A) (X : A) (h : ∀ a, X * E a = E' a * X)
    (S : Finset (Fin n)) : X * ordProd E S = ordProd E' S * X := by
  unfold ordProd
  induction (S.sort (· ≤ ·)) with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, h a, mul_assoc, ih, ← mul_assoc]

/-- **One factor more in an ordered product.** If the `E_a` anticommute in pairs and each
`E_a² = z_a` is central, then `E_a E_S = (−1)^{#{c ∈ S : c < a}} (z_a E_{S∖{a}})` when `a ∈ S`
and `(−1)^{#{c ∈ S : c < a}} E_{S ∪ {a}}` when `a ∉ S`. -/
theorem ordProd_mul_left [Ring A] (E z : Fin n → A)
    (hanti : ∀ a b, a ≠ b → E a * E b = -(E b * E a))
    (hsq : ∀ a, E a * E a = z a) (hz : ∀ a b, Commute (z a) (E b))
    (S : Finset (Fin n)) : ∀ a : Fin n, E a * ordProd E S =
      (-1) ^ (S.filter (· < a)).card *
        (if a ∈ S then z a * ordProd E (S.erase a) else ordProd E (insert a S)) := by
  induction S using Finset.induction_on_min with
  | empty =>
    intro a
    simp [ordProd_singleton]
  | insert m S hm ih =>
    intro a
    have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
    rw [ordProd_insert_min E hm]
    rcases lt_trichotomy a m with hlt | heq | hgt
    · -- `a` below everything: it goes in front
      have hall : ∀ x ∈ insert m S, a < x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hlt
        · exact hlt.trans (hm x hx)
      have haS' : a ∉ insert m S := fun h => lt_irrefl a (hall a h)
      have hfilt : (insert m S).filter (· < a) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]
        exact fun hx => (hall x hx).le
      rw [if_neg haS', hfilt, Finset.card_empty, pow_zero, one_mul, ordProd_insert_min E hall,
        ordProd_insert_min E hm]
    · -- `a = m`: the square
      rw [heq]
      have hfilt : (insert m S).filter (· < m) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false, not_and,
          not_lt]
        rintro (rfl | hx)
        · exact le_rfl
        · exact (hm x hx).le
      rw [if_pos (Finset.mem_insert_self m S), hfilt, Finset.card_empty, pow_zero, one_mul,
        Finset.erase_insert hmS, ← mul_assoc, hsq]
    · -- `m < a`: pass `E_m` with a sign
      have hma : m ≠ a := ne_of_lt hgt
      rw [← mul_assoc, hanti a m (Ne.symm hma), neg_mul, mul_assoc, ih a]
      have hmf : m ∉ S.filter (· < a) := fun h => hmS (Finset.mem_filter.mp h).1
      have hfilt : (insert m S).filter (· < a) = insert m (S.filter (· < a)) := by
        rw [Finset.filter_insert, if_pos hgt]
      rw [hfilt, Finset.card_insert_of_notMem hmf, pow_succ]
      set k := (S.filter (· < a)).card
      have hc : Commute ((-1 : A) ^ k) (E m) := (Commute.neg_one_left _).pow_left _
      by_cases haS : a ∈ S
      · have haS' : a ∈ insert m S := Finset.mem_insert_of_mem haS
        rw [if_pos haS, if_pos haS']
        have hall : ∀ x ∈ S.erase a, m < x := fun x hx => hm x (Finset.mem_of_mem_erase hx)
        rw [Finset.erase_insert_of_ne hma, ordProd_insert_min E hall]
        have h1 : E m * z a = z a * E m := ((hz a m).eq).symm
        rw [← mul_assoc (E m), ← hc.eq, mul_assoc, ← mul_assoc (E m), h1, mul_assoc (z a),
          mul_neg_one, neg_mul]
      · have haS' : a ∉ insert m S := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨Ne.symm hma, haS⟩
        rw [if_neg haS, if_neg haS']
        have hall : ∀ x ∈ insert a S, m < x := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hgt
          · exact hm x hx
        rw [Finset.insert_comm a m S, ordProd_insert_min E hall, ← mul_assoc (E m), ← hc.eq,
          mul_assoc, mul_neg_one, neg_mul]

end Ordered

/-! ## The exterior algebra: words on the set that divides nothing -/

section Exterior

variable {R : Type*} [CommRing R] {n : ℕ}

/-- `(−1)^k` acts on every vector as the number `(−1)^k`. -/
theorem neg_one_pow_end_apply {M : Type*} [AddCommGroup M] [Module R M] (k : ℕ) (v : M) :
    ((-1 : Module.End R M) ^ k) v = ((-1 : R) ^ k) • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply, map_neg, ih,
      pow_succ, mul_neg_one, neg_smul]

/-- Two operators on the sixty-four sets agree when they agree on every `f_S`. -/
theorem endo_ext {f g : Module.End R (Finset (Fin n) → R)}
    (h : ∀ S, f (Pi.single S 1) = g (Pi.single S 1)) : f = g := by
  refine LinearMap.pi_ext' fun S => LinearMap.ext_ring ?_
  simpa using h S

theorem extSign_eq (a : Fin n) (S : Finset (Fin n)) :
    extSign (R := R) a S = (-1) ^ (S.filter (· < a)).card := rfl

theorem extSign_of_min {a : Fin n} {S : Finset (Fin n)} (h : ∀ x ∈ S, a < x) :
    extSign (R := R) a S = 1 := by
  have : S.filter (· < a) = ∅ := by
    ext x
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]
    exact fun hx => (h x hx).le
  rw [extSign_eq, this, Finset.card_empty, pow_zero]

/-- **One direction more on a basis set:** `ε_a f_S = 0` for `a ∈ S`, and
`ε_a f_S = (−1)^{#{c ∈ S : c < a}} f_{S ∪ {a}}` for `a ∉ S`. -/
theorem εx_single (a : Fin n) (S : Finset (Fin n)) :
    εx (R := R) a (Pi.single S 1) =
      if a ∈ S then 0 else extSign (R := R) a S • (Pi.single (insert a S) 1 : Finset (Fin n) → R) := by
  funext T
  simp only [εx_apply, Pi.single_apply]
  by_cases ha : a ∈ S
  · simp only [ha, ↓reduceIte, Pi.zero_apply]
    by_cases hT : a ∈ T
    · have : T.erase a ≠ S := fun h => Finset.notMem_erase a T (h ▸ ha)
      simp [hT, this]
    · simp [hT]
  · simp only [ha, ↓reduceIte, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hT : T = insert a S
    · subst hT
      simp [Finset.erase_insert ha]
    · by_cases haT : a ∈ T
      · have : T.erase a ≠ S := fun h => hT (by rw [← h, Finset.insert_erase haT])
        simp [haT, this, hT]
      · simp [haT, hT]

/-- `ι_a f_∅ = 0`: nothing to remove from the set that divides nothing. -/
theorem ιx_vac (a : Fin n) : ιx (R := R) a (Pi.single ∅ 1) = 0 := by
  funext T
  simp only [ιx_apply, Pi.single_apply, Pi.zero_apply]
  split_ifs with h1 h2
  · rfl
  · exact absurd h2 (Finset.insert_ne_empty a T)
  · simp

/-- The ordered `ε`-word of `S` on `f_∅` is `f_S`. -/
theorem ordProd_εx_vac (S : Finset (Fin n)) :
    ordProd (εx (R := R)) S (Pi.single ∅ 1) = Pi.single S 1 := by
  induction S using Finset.induction_on_min with
  | empty => simp
  | insert m S hm ih =>
    have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
    rw [ordProd_insert_min _ hm, Module.End.mul_apply, ih, εx_single, if_neg hmS,
      extSign_of_min hm, one_smul]

/-- **Proposition 33, the words:** `J_{s₁} J_{s₂} ⋯ J_{s_r} f_∅ = f_{{s₁,…,s_r}}` for
`s₁ < ⋯ < s_r`: the sixty-four sets are the words of the vertical step on the set that divides
nothing. -/
theorem ordProd_Jx_vac (S : Finset (Fin n)) :
    ordProd (Jx (R := R)) S (Pi.single ∅ 1) = Pi.single S 1 := by
  induction S using Finset.induction_on_min with
  | empty => simp
  | insert m S hm ih =>
    have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
    have hsd : symmDiff S {m} = insert m S := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
        · exact Or.inr h1
        · exact Or.inl h1
      · rintro (h1 | h1)
        · exact Or.inr ⟨h1, h1 ▸ hmS⟩
        · exact Or.inl ⟨h1, fun h => hmS (h ▸ h1)⟩
    rw [ordProd_insert_min _ hm, Module.End.mul_apply, ih, Jx_single, Finset.erase_eq_of_notMem hmS,
      hsd, extSign_of_min hm, one_smul]

/-! ## The steps along a vector -/

/-- One direction more along the vector `v`: `ε(v) = Σ_a v_a ε_a`. -/
def εv (v : Fin n → R) : Module.End R (Finset (Fin n) → R) := ∑ a, v a • εx a

/-- One direction fewer along `v`: `ι(v) = Σ_a v_a ι_a`. -/
def ιv (v : Fin n → R) : Module.End R (Finset (Fin n) → R) := ∑ a, v a • ιx a

/-- **The vertical step along `v`:** `J(v) = ε(v) + ι(v)`. -/
def Jv (v : Fin n → R) : Module.End R (Finset (Fin n) → R) := εv v + ιv v

theorem εv_single (a : Fin n) : εv (R := R) (Pi.single a 1) = εx a := by
  simp [εv, Pi.single_apply]

theorem ιv_single (a : Fin n) : ιv (R := R) (Pi.single a 1) = ιx a := by
  simp [ιv, Pi.single_apply]

theorem εv_add (v w : Fin n → R) : εv (v + w) = εv v + εv w := by
  simp [εv, add_smul, Finset.sum_add_distrib]

theorem εv_smul (c : R) (v : Fin n → R) : εv (c • v) = c • εv v := by
  simp [εv, Finset.smul_sum, smul_smul]

theorem ιv_add (v w : Fin n → R) : ιv (v + w) = ιv v + ιv w := by
  simp [ιv, add_smul, Finset.sum_add_distrib]

theorem ιv_smul (c : R) (v : Fin n → R) : ιv (c • v) = c • ιv v := by
  simp [ιv, Finset.smul_sum, smul_smul]

theorem εv_sum {ι : Type*} (s : Finset ι) (v : ι → Fin n → R) :
    εv (∑ i ∈ s, v i) = ∑ i ∈ s, εv (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [εv]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, εv_add, ih]

theorem ιv_sum {ι : Type*} (s : Finset ι) (v : ι → Fin n → R) :
    ιv (∑ i ∈ s, v i) = ∑ i ∈ s, ιv (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ιv]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ιv_add, ih]

/-- A vector is the sum of its components along the directions. -/
theorem vec_eq_sum (v : Fin n → R) : v = ∑ a, v a • (Pi.single a 1 : Fin n → R) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem εv_eq_sum (v : Fin n → R) : εv v = ∑ a, v a • εv (Pi.single a 1) := by
  simp [εv, εv_single]

/-- A double sum `Σ_{a,b} c_ab M_ab` vanishes when `c` is symmetric, `M` antisymmetric and
`M_aa = 0`. -/
theorem sum_sym_antisym {M : Type*} [AddCommGroup M] [Module R M] (c : Fin n → Fin n → R)
    (X : Fin n → Fin n → M) (hc : ∀ a b, c a b = c b a) (hX : ∀ a b, X a b + X b a = 0)
    (hX0 : ∀ a, X a a = 0) : ∑ a, ∑ b, c a b • X a b = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ (fun p _ => Finset.mem_univ _)
    (fun p _ => Prod.swap_swap p)
  · intro p _
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hc p.2 p.1, ← smul_add, hX, smul_zero]
  · intro p _ hp hsw
    apply hp
    have h12 : p.1 = p.2 := by
      have := congrArg Prod.fst hsw
      simpa using this.symm
    rw [h12, hX0, smul_zero]

theorem εv_mul_εv (v w : Fin n → R) :
    εv v * εv w = ∑ a, ∑ b, (v a * w b) • (εx (R := R) a * εx b) := by
  rw [εv, εv, Finset.sum_mul_sum]; simp only [smul_mul_smul_comm]

/-- **`ε(v)² = 0`.** -/
theorem εv_mul_self (v : Fin n → R) : εv v * εv v = 0 := by
  rw [εv_mul_εv]
  exact sum_sym_antisym _ _ (fun a b => mul_comm _ _) (fun a b => εx_εx_add a b)
    (fun a => εx_mul_self a)

/-- **`ε(v)ε(w) + ε(w)ε(v) = 0`.** -/
theorem εv_anticomm (v w : Fin n → R) : εv v * εv w + εv w * εv v = 0 := by
  have h := εv_mul_self (v + w)
  rw [εv_add, add_mul, mul_add, mul_add, εv_mul_self, εv_mul_self, zero_add, add_zero] at h
  exact h

/-- **`ι(v)ε(w) + ε(w)ι(v) = ⟨v, w⟩`.** -/
theorem ιv_εv_add (v w : Fin n → R) :
    ιv v * εv w + εv w * ιv v = (v ⬝ᵥ w) • (1 : Module.End R (Finset (Fin n) → R)) := by
  have e1 : ιv v * εv w = ∑ a, ∑ b, (v a * w b) • (ιx (R := R) a * εx b) := by
    rw [ιv, εv, Finset.sum_mul_sum]; simp only [smul_mul_smul_comm]
  have e2 : εv w * ιv v = ∑ a, ∑ b, (v a * w b) • (εx (R := R) b * ιx a) := by
    have e2' : εv w * ιv v = ∑ b, ∑ a, (w b * v a) • (εx (R := R) b * ιx a) := by
      rw [εv, ιv, Finset.sum_mul_sum]; simp only [smul_mul_smul_comm]
    rw [e2', Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]
  have key : ∀ a b : Fin n, ιx (R := R) a * εx b + εx b * ιx a = if b = a then 1 else 0 := by
    intro a b
    rw [add_comm]
    exact εx_ιx_add b a
  have e3 : ∀ a : Fin n, ∑ b, (v a * w b) • (ιx (R := R) a * εx b) +
      ∑ b, (v a * w b) • (εx (R := R) b * ιx a) = (v a * w a) • 1 := by
    intro a
    rw [← Finset.sum_add_distrib]
    simp_rw [← smul_add, key, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ a)]
  rw [e1, e2, ← Finset.sum_add_distrib]
  simp_rw [e3]
  rw [dotProduct, Finset.sum_smul]

/-- **`ι(v)ι(w) + ι(w)ι(v) = 0`.** -/
theorem ιv_anticomm (v w : Fin n → R) : ιv v * ιv w + ιv w * ιv v = 0 := by
  have hsq : ∀ u : Fin n → R, ιv u * ιv u = 0 := by
    intro u
    have : ιv u * ιv u = ∑ a, ∑ b, (u a * u b) • (ιx (R := R) a * ιx b) := by
      rw [ιv, Finset.sum_mul_sum]; simp only [smul_mul_smul_comm]
    rw [this]
    exact sum_sym_antisym _ _ (fun a b => mul_comm _ _) (fun a b => ιx_ιx_add a b)
      (fun a => ιx_mul_self a)
  have h := hsq (v + w)
  rw [ιv_add, add_mul, mul_add, mul_add, hsq, hsq, zero_add, add_zero] at h
  exact h

/-- **`J(v)J(w) + J(w)J(v) = 2⟨v, w⟩`.** -/
theorem Jv_anticomm (v w : Fin n → R) :
    Jv v * Jv w + Jv w * Jv v = (2 * (v ⬝ᵥ w)) • (1 : Module.End R (Finset (Fin n) → R)) := by
  have h4 := ιv_εv_add w v
  rw [dotProduct_comm] at h4
  calc Jv v * Jv w + Jv w * Jv v
      = (εv v * εv w + εv w * εv v) + (ιv v * ιv w + ιv w * ιv v) +
          (ιv v * εv w + εv w * ιv v) + (ιv w * εv v + εv v * ιv w) := by
        simp only [Jv, add_mul, mul_add]
        abel
    _ = (2 * (v ⬝ᵥ w)) • 1 := by
        rw [εv_anticomm, ιv_anticomm, ιv_εv_add, h4, zero_add, zero_add, two_mul, add_smul]

/-- **`J(v)² = |v|²`.** -/
theorem Jv_mul_self (v : Fin n → R) :
    Jv v * Jv v = (v ⬝ᵥ v) • (1 : Module.End R (Finset (Fin n) → R)) := by
  have h3 := ιv_εv_add v v
  simp only [Jv, add_mul, mul_add, εv_mul_self]
  have h2 : ιv v * ιv v = 0 := by
    have := ιv_anticomm v v
    have hsq : ιv v * ιv v = ∑ a, ∑ b, (v a * v b) • (ιx (R := R) a * ιx b) := by
      rw [ιv, Finset.sum_mul_sum]; simp only [smul_mul_smul_comm]
    rw [hsq]
    exact sum_sym_antisym _ _ (fun a b => mul_comm _ _) (fun a b => ιx_ιx_add a b)
      (fun a => ιx_mul_self a)
  rw [h2, ← h3]
  abel

/-! ## The action of a matrix on the sixty-four sets -/

/-- The columns of `O`, stepped: `E_a = ε(Oe_a)`. -/
def colStep (O : Matrix (Fin n) (Fin n) R) (a : Fin n) : Module.End R (Finset (Fin n) → R) :=
  εv (O.col a)

/-- **`Λ(O)`**, the action of `O` on the sixty-four sets: `Λ(O) f_S = Oe_{s₁} ∧ ⋯ ∧ Oe_{s_r}`. -/
def extMap (O : Matrix (Fin n) (Fin n) R) : Module.End R (Finset (Fin n) → R) :=
  Matrix.mulVecLin (Matrix.of fun T S => ordProd (colStep O) S (Pi.single ∅ 1) T)

theorem extMap_single (O : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)) :
    extMap O (Pi.single S 1) = ordProd (colStep O) S (Pi.single ∅ 1) := by
  rw [extMap, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  rfl

theorem extMap_vac (O : Matrix (Fin n) (Fin n) R) :
    extMap O (Pi.single ∅ 1) = Pi.single ∅ 1 := by
  rw [extMap_single, ordProd_empty, Module.End.one_apply]

theorem colStep_anti (O : Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    colStep O a * colStep O b = -(colStep O b * colStep O a) :=
  eq_neg_of_add_eq_zero_left (εv_anticomm _ _)

theorem colStep_sq (O : Matrix (Fin n) (Fin n) R) (a : Fin n) :
    colStep O a * colStep O a = 0 :=
  εv_mul_self _

/-- The ordered `ε(Oe)`-word of `S`, with one factor more. -/
theorem colStep_mul_ordProd (O : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)) (a : Fin n) :
    colStep O a * ordProd (colStep O) S =
      (-1) ^ (S.filter (· < a)).card * (if a ∈ S then 0 else ordProd (colStep O) (insert a S)) := by
  rw [ordProd_mul_left (colStep O) (fun _ => 0) (fun a b _ => colStep_anti O a b)
    (colStep_sq O) (fun _ _ => Commute.zero_left _) S a]
  simp only [zero_mul]

/-- **`Λ(O) ε_a = ε(Oe_a) Λ(O)`** for every matrix `O`: one direction more is carried by `O`. -/
theorem extMap_εx (O : Matrix (Fin n) (Fin n) R) (a : Fin n) :
    extMap O * εx a = colStep O a * extMap O := by
  refine endo_ext fun S => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, εx_single, extMap_single, ← Module.End.mul_apply,
    colStep_mul_ordProd]
  by_cases ha : a ∈ S
  · simp [ha]
  · rw [if_neg ha, if_neg ha, map_smul, extMap_single, Module.End.mul_apply,
      neg_one_pow_end_apply, extSign_eq]

/-- `O v` is the sum of the columns of `O` weighted by `v`. -/
theorem mulVec_eq_sum_col (O : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    O *ᵥ v = ∑ a, v a • O.col a := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.col_apply, mul_comm]

/-- `Λ(O) ε(v) = ε(Ov) Λ(O)`. -/
theorem extMap_εv (O : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    extMap O * εv v = εv (O *ᵥ v) * extMap O := by
  have h1 : εv (O *ᵥ v) = ∑ a, v a • colStep O a := by
    rw [mulVec_eq_sum_col, εv_sum]
    simp only [εv_smul, colStep]
  rw [h1, εv, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, extMap_εx]

theorem col_mul (O P : Matrix (Fin n) (Fin n) R) (a : Fin n) :
    (O * P).col a = O *ᵥ P.col a := by
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col_apply]

theorem extMap_colStep (O P : Matrix (Fin n) (Fin n) R) (a : Fin n) :
    extMap O * colStep P a = colStep (O * P) a * extMap O := by
  rw [colStep, colStep, extMap_εv, col_mul]

/-- **`Λ(OP) = Λ(O)Λ(P)`.** -/
theorem extMap_mul (O P : Matrix (Fin n) (Fin n) R) : extMap (O * P) = extMap O * extMap P := by
  refine endo_ext fun S => ?_
  have h := ordProd_intertwine (colStep P) (colStep (O * P)) (extMap O) (extMap_colStep O P) S
  rw [Module.End.mul_apply, extMap_single, extMap_single, ← Module.End.mul_apply, h,
    Module.End.mul_apply, extMap_vac]

theorem col_one (a : Fin n) : (1 : Matrix (Fin n) (Fin n) R).col a = Pi.single a 1 := by
  funext i
  simp [Matrix.col_apply, Matrix.one_apply, Pi.single_apply]

/-- **`Λ(1) = 1`.** -/
theorem extMap_one : extMap (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  refine endo_ext fun S => ?_
  rw [extMap_single, Module.End.one_apply]
  have : ordProd (colStep (1 : Matrix (Fin n) (Fin n) R)) S = ordProd εx S := by
    refine ordProd_congr fun a _ => ?_
    rw [colStep, col_one, εv_single]
  rw [this, ordProd_εx_vac]

/-- `ι(v)` kills the set that divides nothing. -/
theorem ιv_vac (v : Fin n → R) : ιv v (Pi.single ∅ 1) = 0 := by
  simp [ιv, LinearMap.sum_apply, ιx_vac]

/-- **`Λ(O) ι_a = ι(Oe_a) Λ(O)`** for every orthogonal `O`: one direction fewer is carried too. -/
theorem extMap_ιx (O : Matrix (Fin n) (Fin n) R) (hO : Oᵀ * O = 1) (a : Fin n) :
    extMap O * ιx a = ιv (O.col a) * extMap O := by
  have hdot : ∀ b c : Fin n, O.col b ⬝ᵥ O.col c = if b = c then 1 else 0 := by
    intro b c
    have := congrFun (congrFun hO b) c
    simpa [Matrix.mul_apply, dotProduct, Matrix.col_apply, Matrix.one_apply] using this
  refine endo_ext fun S => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  induction S using Finset.induction_on with
  | empty => rw [ιx_vac, map_zero, extMap_vac, ιv_vac]
  | insert m S hmS ih =>
    -- `f_{S ∪ {m}} = ± ε_m f_S`
    have hf : (Pi.single (insert m S) 1 : Finset (Fin n) → R) =
        extSign (R := R) m S • εx m (Pi.single S 1) := by
      rw [εx_single, if_neg hmS, smul_smul, extSign_mul_self, one_smul]
    have hιε : ιx (R := R) a * εx m = (if m = a then 1 else 0) - εx m * ιx a := by
      rw [← εx_ιx_add m a]
      abel
    have hιε' : ιv (O.col a) * colStep O m =
        (O.col a ⬝ᵥ O.col m) • 1 - colStep O m * ιv (O.col a) := by
      rw [colStep, ← ιv_εv_add]
      abel
    set f : Finset (Fin n) → R := Pi.single S 1 with hfdef
    have hL : extMap O (ιx a (εx m f)) =
        (if m = a then extMap O f else 0) - colStep O m (ιv (O.col a) (extMap O f)) := by
      have e1 : ιx a (εx m f) = (if m = a then f else 0) - εx m (ιx a f) := by
        rw [← Module.End.mul_apply (ιx a) (εx m), hιε, LinearMap.sub_apply, Module.End.mul_apply]
        split_ifs <;> simp
      rw [e1, map_sub, ← Module.End.mul_apply (extMap O) (εx m), extMap_εx, Module.End.mul_apply,
        ih]
      split_ifs <;> simp
    have hR : ιv (O.col a) (extMap O (εx m f)) =
        (O.col a ⬝ᵥ O.col m) • extMap O f - colStep O m (ιv (O.col a) (extMap O f)) := by
      rw [← Module.End.mul_apply (extMap O) (εx m), extMap_εx, Module.End.mul_apply,
        ← Module.End.mul_apply (ιv (O.col a)) (colStep O m), hιε', LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply]
    rw [hf, map_smul, map_smul, map_smul, map_smul, hL, hR, hdot a m]
    congr 2
    split_ifs with h1 h2 h2
    · rw [one_smul]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [zero_smul]

/-- `Λ(O) ι(v) = ι(Ov) Λ(O)` for orthogonal `O`. -/
theorem extMap_ιv (O : Matrix (Fin n) (Fin n) R) (hO : Oᵀ * O = 1) (v : Fin n → R) :
    extMap O * ιv v = ιv (O *ᵥ v) * extMap O := by
  have hOv : O *ᵥ v = ∑ a, v a • O.col a := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.col_apply, mul_comm]
  rw [hOv, ιv_sum]
  simp only [ιv_smul]
  conv_lhs => rw [ιv, Finset.mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, extMap_ιx O hO a]

/-- `Λ(O) J(v) = J(Ov) Λ(O)` for orthogonal `O`. -/
theorem extMap_Jv (O : Matrix (Fin n) (Fin n) R) (hO : Oᵀ * O = 1) (v : Fin n → R) :
    extMap O * Jv v = Jv (O *ᵥ v) * extMap O := by
  rw [Jv, Jv, mul_add, add_mul, extMap_εv, extMap_ιv O hO]

/-- **`Λ(O)⁻¹ = Λ(Oᵀ)`** for orthogonal `O`. -/
theorem extMap_mul_transpose (O : Matrix (Fin n) (Fin n) R) (hO : Oᵀ * O = 1) :
    extMap O * extMap Oᵀ = 1 ∧ extMap Oᵀ * extMap O = 1 := by
  have hO' : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  refine ⟨?_, ?_⟩
  · rw [← extMap_mul, hO', extMap_one]
  · rw [← extMap_mul, hO, extMap_one]

/-- **Proposition 33, the covariance:** `Λ(O) J(v) Λ(O)⁻¹ = J(Ov)` for every orthogonal `O`, with
`Λ(O)⁻¹ = Λ(Oᵀ)`. -/
theorem extMap_conj_Jv (O : Matrix (Fin n) (Fin n) R) (hO : Oᵀ * O = 1) (v : Fin n → R) :
    extMap O * Jv v * extMap Oᵀ = Jv (O *ᵥ v) := by
  rw [extMap_Jv O hO, mul_assoc, (extMap_mul_transpose O hO).1, mul_one]

/-- The same for `ε` alone, for every invertible `O`: `Λ(O) ε(v) Λ(O)⁻¹ = ε(Ov)`. -/
theorem extMap_conj_εv (O O' : Matrix (Fin n) (Fin n) R) (hO : O * O' = 1) (v : Fin n → R) :
    extMap O * εv v * extMap O' = εv (O *ᵥ v) := by
  rw [extMap_εv, mul_assoc, ← extMap_mul, hO, extMap_one, mul_one]

end Exterior

/-! ## The rotations of the six act by invertible operators -/

section Units

variable {n : ℕ}

theorem orthogonal_transpose_mul {O : Matrix (Fin n) (Fin n) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin n) ℝ) : Oᵀ * O = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hO

/-- **`O ↦ Λ(O)`**, a homomorphism from the orthogonal group of the six into the invertible
operators on the sixty-four sets. -/
noncomputable def extUnits : Matrix.orthogonalGroup (Fin n) ℝ →*
    (Module.End ℝ (Finset (Fin n) → ℝ))ˣ where
  toFun O :=
    { val := extMap (O : Matrix (Fin n) (Fin n) ℝ)
      inv := extMap (O : Matrix (Fin n) (Fin n) ℝ)ᵀ
      val_inv := (extMap_mul_transpose _ (orthogonal_transpose_mul O.2)).1
      inv_val := (extMap_mul_transpose _ (orthogonal_transpose_mul O.2)).2 }
  map_one' := by
    ext1
    simp [extMap_one]
  map_mul' O P := by
    ext1
    simp [extMap_mul]

theorem extUnits_val (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    ((extUnits O : (Module.End ℝ (Finset (Fin n) → ℝ))ˣ) : Module.End ℝ (Finset (Fin n) → ℝ)) =
      extMap (O : Matrix (Fin n) (Fin n) ℝ) := rfl

/-- **Proposition 33:** `Λ(O) J(v) Λ(O)⁻¹ = J(Ov)` for every rotation `O`. -/
theorem extUnits_conj_Jv (O : Matrix.orthogonalGroup (Fin n) ℝ) (v : Fin n → ℝ) :
    (extUnits O : Module.End ℝ (Finset (Fin n) → ℝ)) * Jv v *
        ((extUnits O)⁻¹ : (Module.End ℝ (Finset (Fin n) → ℝ))ˣ) =
      Jv ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) :=
  extMap_conj_Jv _ (orthogonal_transpose_mul O.2) v

end Units

end Comparison

end
