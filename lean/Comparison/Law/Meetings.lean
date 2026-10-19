module

public import Comparison.Law.Rule

/-!
# The law, III: the step and the agreement exchanged; the meeting's factor (Propositions 130, 131)

The sixteen two-spinor states `U : Fin 16` are the meetings, `T_U = disagreeSet U` the lines on which the
two systems disagree, `ε_t(U) = (−1)^{[t ∈ T_U]}` the agreement sign (`charSign`), `θ_U = diag ε(U)`.
The character transform is `𝒳_{UV} = (−1)^{|T_U ∩ T_V|}/4` (`charX`); on the eighty states it is
`𝒳 ⊗ 1` (`charX80`).

**Proposition 130.**
* `charX_mul_self`: `𝒳² = 1`; `charX_transition_charX`: **`𝒳 X_t 𝒳 = diag ε_t`**, one line stepping on
  one system is, at the meetings, the agreement of the two systems on that line;
  `charX_adjacency_charX`: `𝒳 A 𝒳 = diag(L − 1)`, the values `5, 1, −3`.
* `conj_transitionShaped`: every operator `(x, a) ← (y, b)` of the form `[x = T_a(y)] c_ab` becomes, meeting
  by meeting, `θ_U c`.
* `prop130_B`: **`(𝒳 ⊗ 1) B (𝒳 ⊗ 1) = ⊕_U K_U`**, `K_U = θ_U(𝐉 − I)`; `prop130_R`: the undo becomes
  `⊕_U θ_U`; `prop130_coin`: **the coin `(2/5)B − (3/5)R` becomes `⊕_U θ_U σ`**;
  `theta_coin_orthogonal`: each `θ_U σ` is orthogonal; `thetaP_compl`: `θ_{U^c} = −θ_U`.

**Proposition 131 and the Euler completion, equation (1).**
* `euler_completion`: **for any five weights `c_t` in any commutative ring,
  `det[I − uD(𝐉 − I)] = ∏_t (1 + uc_t) − u Σ_t c_t ∏_{s≠t}(1 + uc_s)`**;
  `euler_completion_deriv`: over `ℂ` this is **`(1 − u d/du) det(I + uD)`**.
* `meeting_factor`: for signs `ε_t² = 1`,
  `(1 − u²) det(I − uθ(𝐉 − I)) = ∏_t(1 + uε_t) · (1 + 4u² − u Σ_t ε_t)`;
  `pattern_factor`: **at every one of the 32 patterns** `V` (`a = 5 − |V|`, `d = |V|`),
  `(1 − u²) det(I − uK_V) = (1 + u)^a (1 − u)^d (1 + 4u² − u(a − d))`;
  `pattern_factor_cancelled`: `det(I − uK_V) = (1 + u)^{a−1}(1 − u)^{d−1}(1 + 4u² − u(a − d))` for
  `a, d ≥ 1`; `singlet_factor`, `all_factor`: `(1 + u)⁴(1 − 4u)` and `(1 − u)⁴(1 + 4u)` at `d = 0, 5`.
* `sum_agree_minus_one`: `Σ_U (a_U − 1) = Σ_U (d_U − 1) = 24` over the sixteen meetings.
* `law_meetings`: **the sixteen meetings multiply to the law, `∏_U det(I − uK_U) = det(I − uB)`**;
  `law_twins`: the sixteen counterparts multiply to `det(I + uB)`; `law_meetings_closed`: with
  Proposition 54, `= (1 − u²)²⁴ ∏_U (1 + 4u² − uλ_U)`.
-/

@[expose] public section

namespace Comparison

open Matrix Kronecker

namespace Law

/-! ## The character transform and the meetings -/

section Meetings

variable (K : Type*) [Field K] [CharZero K]

/-- **The character transform** `𝒳_{UV} = (−1)^{|T_U ∩ T_V|}/4`. -/
def charX : Matrix (Fin 16) (Fin 16) K := Matrix.of fun U V => (charTable U V : K) / 4

/-- **The agreement sign** `ε_t(U)`: `+1` where the two systems agree on the line `t`, `−1` where they
disagree. -/
def agreeSign (U : Fin 16) (t : Fin 5) : K := (charSign t U : K)

/-- `θ_U = diag ε(U)` on the five directions. -/
def thetaM (U : Fin 16) : Matrix (Fin 5) (Fin 5) K := diagonal (agreeSign K U)

/-- The all-ones matrix `𝐉` on the five directions. -/
def onesM : Matrix (Fin 5) (Fin 5) K := Matrix.of fun _ _ => 1

/-- **The last-step direction's walk at the meeting** `K_U = θ_U(𝐉 − I)`. -/
def lastDirectionK (U : Fin 16) : Matrix (Fin 5) (Fin 5) K := thetaM K U * (onesM K - 1)

/-- The sixteen meetings assembled, block `U` on the five directions. -/
def meetBlocks (M : Fin 16 → Matrix (Fin 5) (Fin 5) K) : Matrix State State K :=
  Matrix.of fun p q => if p.1 = q.1 then M p.1 p.2 q.2 else 0

/-- The character transform on the eighty states, `𝒳 ⊗ 1`. -/
def charX80 : Matrix State State K := charX K ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) K)

/-- An operator on the eighty states that moves the vertex by the line it goes along:
`((x, a), (y, b)) ↦ [x = T_a(y)] c_ab`. -/
def transitionShaped (c : Fin 5 → Fin 5 → K) : Matrix State State K :=
  Matrix.of fun p q => if p.1 = transition p.2 q.1 then c p.2 q.2 else 0

/-- The transition of the line `t` on the sixteen vertices, over `K`. -/
def transitionK (t : Fin 5) : Matrix (Fin 16) (Fin 16) K :=
  Matrix.of fun x y => if x = transition t y then 1 else 0

theorem charTable_transition : ∀ (t : Fin 5) (x U : Fin 16),
    charTable (transition t x) U = charTable x U * charSign t U := by
  decide +kernel

theorem charTable_symm (x U : Fin 16) : charTable x U = charTable U x := by
  rw [charTable_eq]
  simp only [Matrix.of_apply, Finset.inter_comm]

theorem charX_symm (x U : Fin 16) : charX K x U = charX K U x := by
  simp only [charX, Matrix.of_apply, charTable_symm x U]

theorem charX_transition (t : Fin 5) (x U : Fin 16) :
    charX K (transition t x) U = charX K x U * agreeSign K U t := by
  simp only [charX, agreeSign, Matrix.of_apply, charTable_transition t x U]
  push_cast
  ring

/-- **`𝒳² = 1`.** -/
theorem charX_mul_self : charX K * charX K = 1 := by
  ext U W
  have h := congrArg (fun M : Matrix (Fin 16) (Fin 16) ℤ => ((M U W : ℤ) : K)) charTable_mul_self
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  push_cast at h
  simp only [Matrix.mul_apply, charX, Matrix.of_apply, Matrix.one_apply]
  have e : ∑ x, (charTable U x : K) / 4 * ((charTable x W : K) / 4) =
      (∑ x, (charTable U x : K) * (charTable x W : K)) / 16 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [e, h]
  split_ifs <;> simp

theorem charX80_mul_self : charX80 K * charX80 K = 1 := by
  rw [charX80, ← Matrix.mul_kronecker_mul, charX_mul_self, Matrix.mul_one,
    Matrix.one_kronecker_one]

theorem det_charX80_sq : (charX80 K).det ^ 2 = 1 := by
  rw [sq, ← det_mul, charX80_mul_self, det_one]

/-- `M 𝒳 = 𝒳 ⊕_U θ_U c` for a transition-shaped `M`. -/
theorem transitionShaped_mul_charX80 (c : Fin 5 → Fin 5 → K) :
    transitionShaped K c * charX80 K =
      charX80 K * meetBlocks K (fun U => thetaM K U * Matrix.of c) := by
  ext ⟨x, a⟩ ⟨V, b⟩
  have hL : (transitionShaped K c * charX80 K) (x, a) (V, b) = c a b * charX K (transition a x) V := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (transition a x)]
    · rw [Finset.sum_eq_single b]
      · simp [transitionShaped, charX80, transition_transition]
      · intro b' _ hb'
        simp [charX80, Matrix.one_apply, hb']
      · simp
    · intro y _ hy
      have hxy : ¬ x = transition a y := fun h => hy (by rw [h, transition_transition])
      refine Finset.sum_eq_zero fun b' _ => ?_
      simp [transitionShaped, hxy]
    · simp
  have hR : (charX80 K * meetBlocks K (fun U => thetaM K U * Matrix.of c)) (x, a) (V, b) =
      charX K x V * (agreeSign K V a * c a b) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single V]
    · rw [Finset.sum_eq_single a]
      · simp [charX80, meetBlocks, thetaM, Matrix.diagonal_mul]
      · intro a' _ ha'
        simp [charX80, Matrix.one_apply, Ne.symm ha']
      · simp
    · intro W _ hW
      refine Finset.sum_eq_zero fun a' _ => ?_
      simp [meetBlocks, hW]
    · simp
  rw [hL, hR, charX_transition]
  ring

/-- **The transition-shaped operators become the meetings' blocks:**
`(𝒳 ⊗ 1) M (𝒳 ⊗ 1) = ⊕_U θ_U c`. -/
theorem conj_transitionShaped (c : Fin 5 → Fin 5 → K) :
    charX80 K * transitionShaped K c * charX80 K = meetBlocks K (fun U => thetaM K U * Matrix.of c) := by
  rw [Matrix.mul_assoc, transitionShaped_mul_charX80, ← Matrix.mul_assoc, charX80_mul_self,
    Matrix.one_mul]

/-- **`𝒳 X_t 𝒳 = diag ε_t`.** -/
theorem charX_transition_charX (t : Fin 5) :
    charX K * transitionK K t * charX K = diagonal fun U => agreeSign K U t := by
  have h : transitionK K t * charX K = charX K * diagonal fun U => agreeSign K U t := by
    ext x V
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [transitionK, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (transition t x)]
    · simp only [transition_transition, ↓reduceIte, charX_transition]
    · intro y _ hy
      have hxy : ¬ x = transition t y := by
        intro h
        apply hy
        rw [h, transition_transition]
      simp [hxy]
    · simp
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, charX_mul_self, Matrix.one_mul]

/-- **`𝒳 A 𝒳 = L − 1`:** the walk on the sixteen vertices is, at the meetings, the agreements less the
disagreements, `a − d = 5, 1, −3`. -/
theorem charX_adjacency_charX :
    charX K * (∑ t, transitionK K t) * charX K = diagonal fun U => (charValue U : K) := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp only [charX_transition_charX]
  ext U V
  simp only [Matrix.sum_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    simp only [agreeSign, charValue, charSign]
    have : ∀ U : Fin 16, (∑ t : Fin 5, ((if t ∈ disagreeSet U then -1 else 1 : ℤ) : K)) =
        ((5 - 2 * (disagreeSet U).card : ℤ) : K) := by
      intro U
      rw [← Int.cast_sum]
      congr 1
      revert U
      decide
    rw [this]
  · simp

/-- The agreements less the disagreements: `Σ_t ε_t(U) = L(e_U) − 1`. -/
theorem sum_agreeSign (U : Fin 16) : ∑ t, agreeSign K U t = (Lvalue U : K) - 1 := by
  have : ∀ U : Fin 16, (∑ t : Fin 5, (charSign t U : ℤ)) = Lvalue U - 1 := by decide
  simp only [agreeSign]
  rw [← Int.cast_sum, this U]
  push_cast
  ring

end Meetings

/-! ## Proposition 130 on the eighty states -/

theorem contB_eq_transitionShaped : contB = transitionShaped ℚ (fun a b => if a = b then 0 else 1) := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [contB, transitionShaped, Continues, Matrix.of_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · by_cases hx : x = transition a y
    · simp [hab, hx]
    · simp [hab, hx]

theorem undoR_eq_transitionShaped : undoR = transitionShaped ℚ (fun a b => if a = b then 1 else 0) := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [undoR, undoState, transitionShaped, Matrix.of_apply, Prod.mk.injEq]
  by_cases hab : a = b
  · subst hab
    by_cases hx : x = transition a y <;> simp [hx]
  · simp [hab]

theorem stepU_eq_transitionShaped : stepU = transitionShaped ℚ (fun a b => coin a b) := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [stepU, transitionShaped, Matrix.of_apply]

theorem of_offDiag : (Matrix.of fun a b : Fin 5 => if a = b then (0 : ℚ) else 1) = onesM ℚ - 1 := by
  ext a b
  simp only [Matrix.of_apply, onesM, Matrix.sub_apply, Matrix.one_apply]
  split_ifs <;> norm_num

theorem of_diag : (Matrix.of fun a b : Fin 5 => if a = b then (1 : ℚ) else 0) = 1 := by
  ext a b
  simp only [Matrix.of_apply, Matrix.one_apply]

/-- **Proposition 130, the step:** `(𝒳 ⊗ 1) B (𝒳 ⊗ 1) = ⊕_U K_U`, `K_U = θ_U(𝐉 − I)`: at each
meeting the last-step direction walks the five directions with the meeting's signs. -/
theorem prop130_B : charX80 ℚ * contB * charX80 ℚ = meetBlocks ℚ (lastDirectionK ℚ) := by
  rw [contB_eq_transitionShaped, conj_transitionShaped, of_offDiag]
  rfl

/-- **Proposition 130, the undo:** `(𝒳 ⊗ 1) R (𝒳 ⊗ 1) = ⊕_U θ_U`: the meeting's division. -/
theorem prop130_R : charX80 ℚ * undoR * charX80 ℚ = meetBlocks ℚ (thetaM ℚ) := by
  rw [undoR_eq_transitionShaped, conj_transitionShaped, of_diag]
  simp only [Matrix.mul_one]

/-- **Proposition 130, the coin at the meetings:** `(𝒳 ⊗ 1)((2/5)B − (3/5)R)(𝒳 ⊗ 1) = ⊕_U θ_U σ`. -/
theorem prop130_coin :
    charX80 ℚ * ((2 / 5 : ℚ) • contB - (3 / 5 : ℚ) • undoR) * charX80 ℚ =
      meetBlocks ℚ (fun U => thetaM ℚ U * coin) := by
  rw [← stepU_eq, stepU_eq_transitionShaped, conj_transitionShaped]
  have : (Matrix.of fun a b : Fin 5 => coin a b) = coin := by
    ext a b
    rfl
  rw [this]

/-- Each meeting's coin `θ_U σ` is orthogonal. -/
theorem theta_coin_orthogonal (U : Fin 16) : (thetaM ℚ U * coin)ᵀ * (thetaM ℚ U * coin) = 1 := by
  have hθ : (thetaM ℚ U)ᵀ * thetaM ℚ U = 1 := by
    rw [thetaM, diagonal_transpose, diagonal_mul_diagonal]
    ext a b
    simp only [diagonal_apply, Matrix.one_apply, agreeSign, charSign]
    split_ifs <;> norm_num
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (thetaM ℚ U)ᵀ, hθ,
    Matrix.one_mul, coin_orthogonal]

/-- The sign pattern of any set `V` of the five directions: `θ_V = diag((−1)^{[t ∈ V]})`. -/
def thetaP {R : Type*} [CommRing R] (V : Finset (Fin 5)) : Matrix (Fin 5) (Fin 5) R :=
  diagonal fun t => if t ∈ V then -1 else 1

/-- **The counterpart carries the opposite signs:** `θ_{V^c} = −θ_V`. -/
theorem thetaP_compl {R : Type*} [CommRing R] (V : Finset (Fin 5)) :
    thetaP (R := R) Vᶜ = -thetaP V := by
  ext a b
  simp only [thetaP, diagonal_apply, Matrix.neg_apply, Finset.mem_compl]
  split_ifs <;> simp_all

/-- The meeting's `θ_U` is the pattern of its disagreement set. -/
theorem thetaM_eq_thetaP (U : Fin 16) : thetaM ℚ U = thetaP (disagreeSet U) := by
  ext a b
  simp only [thetaM, thetaP, diagonal_apply, agreeSign, charSign]
  split_ifs <;> simp

/-! ## Equation (1): the Euler completion -/

theorem prod_erase_ite {R : Type*} [CommRing R] (f : Fin 5 → R) (t : Fin 5) :
    ∏ s ∈ Finset.univ.erase t, f s = ∏ s, if s ≠ t then f s else 1 := by
  rw [← Finset.filter_ne', Finset.prod_filter]

/-- **The Euler completion** (equation (1)), for any five weights `c_t` in any commutative ring:
`det[I − uD(𝐉 − I)] = ∏_t (1 + uc_t) − u Σ_t c_t ∏_{s≠t}(1 + uc_s)`. -/
theorem euler_completion {R : Type*} [CommRing R] (u : R) (c : Fin 5 → R) :
    (1 - u • (diagonal c * (Matrix.of fun i j : Fin 5 => if i = j then (0 : R) else 1))).det =
      ∏ t, (1 + u * c t) - u * ∑ t, c t * ∏ s ∈ Finset.univ.erase t, (1 + u * c s) := by
  simp only [prod_erase_ite]
  simp only [det_succ_row_zero, Fin.sum_univ_succ, Fin.prod_univ_succ, submatrix_apply,
    Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, Fin.zero_succAbove,
    Fin.succ_zero_eq_one, det_unique, Fin.default_eq_zero, Fin.prod_univ_zero, Fin.sum_univ_zero,
    Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, mul_apply, diagonal_apply, of_apply,
    smul_eq_mul]
  simp [Fin.succAbove, Fin.lt_def]
  ring

/-- `det(I + uD) = ∏_t (1 + uc_t)`, the exterior character of the meeting. -/
theorem det_one_add_diag {R : Type*} [CommRing R] (u : R) (c : Fin 5 → R) :
    (1 + u • diagonal c).det = ∏ t, (1 + u * c t) := by
  have : (1 + u • diagonal c : Matrix (Fin 5) (Fin 5) R) = diagonal fun t => 1 + u * c t := by
    ext i j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [this, det_diagonal]

/-- **Equation (1):** over `ℂ`, `det[I − uD(𝐉 − I)] = (1 − u d/du) det(I + uD)` for any complex
weights. -/
theorem euler_completion_deriv (c : Fin 5 → ℂ) (u : ℂ) :
    HasDerivAt (fun v : ℂ => (1 + v • diagonal c).det)
        (∑ t, c t * ∏ s ∈ Finset.univ.erase t, (1 + u * c s)) u ∧
      (1 - u • (diagonal c * (Matrix.of fun i j : Fin 5 => if i = j then (0 : ℂ) else 1))).det =
        (1 + u • diagonal c).det -
          u * deriv (fun v : ℂ => (1 + v • diagonal c).det) u := by
  have hfun : (fun v : ℂ => (1 + v • diagonal c).det) = fun v => ∏ t, (1 + v * c t) := by
    funext v
    exact det_one_add_diag v c
  have hd : HasDerivAt (fun v : ℂ => ∏ t, (1 + v * c t))
      (∑ t, c t * ∏ s ∈ Finset.univ.erase t, (1 + u * c s)) u := by
    have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun t v => 1 + v * c t)
      (f' := fun t => c t) (x := u) (fun t _ => by
        simpa using ((hasDerivAt_id u).mul_const (c t)).const_add 1)
    convert h using 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hfun]
  refine ⟨hd, ?_⟩
  rw [hd.deriv, euler_completion, det_one_add_diag]

/-! ## Proposition 131: the meeting's factor -/

/-- **The meeting's factor:** for signs `ε_t² = 1`,
`(1 − u²) det(I − uθ(𝐉 − I)) = ∏_t(1 + uε_t)·(1 + 4u² − u Σ_t ε_t)`. -/
theorem meeting_factor {R : Type*} [CommRing R] (u : R) (ε : Fin 5 → R) (hε : ∀ t, ε t ^ 2 = 1) :
    (1 - u ^ 2) *
        (1 - u • (diagonal ε * (Matrix.of fun i j : Fin 5 => if i = j then (0 : R) else 1))).det =
      (∏ t, (1 + u * ε t)) * (1 + 4 * u ^ 2 - u * ∑ t, ε t) := by
  rw [euler_completion]
  have key : ∀ t, (1 - u ^ 2) * (ε t * ∏ s ∈ Finset.univ.erase t, (1 + u * ε s)) =
      (ε t - u) * ∏ s, (1 + u * ε s) := by
    intro t
    rw [← Finset.mul_prod_erase Finset.univ (fun s => 1 + u * ε s) (Finset.mem_univ t)]
    have h1 : (1 - u ^ 2) * ε t = (ε t - u) * (1 + u * ε t) := by
      linear_combination (-u) * hε t
    calc (1 - u ^ 2) * (ε t * ∏ s ∈ Finset.univ.erase t, (1 + u * ε s))
        = ((1 - u ^ 2) * ε t) * ∏ s ∈ Finset.univ.erase t, (1 + u * ε s) := by ring
      _ = ((ε t - u) * (1 + u * ε t)) * ∏ s ∈ Finset.univ.erase t, (1 + u * ε s) := by rw [h1]
      _ = _ := by ring
  have hsum : (1 - u ^ 2) * ∑ t, ε t * ∏ s ∈ Finset.univ.erase t, (1 + u * ε s) =
      (∑ t, ε t - 5 * u) * ∏ s, (1 + u * ε s) := by
    rw [Finset.mul_sum]
    simp only [key]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    simp
  linear_combination (-u) * hsum

/-- The exterior character of a pattern: `∏_t(1 + uε_t(V)) = (1 + u)^{5−|V|} (1 − u)^{|V|}`. -/
theorem prod_pattern {R : Type*} [CommRing R] (u : R) (V : Finset (Fin 5)) :
    ∏ t, (1 + u * (if t ∈ V then -1 else 1 : R)) = (1 + u) ^ (5 - V.card) * (1 - u) ^ V.card := by
  have h : ∀ t, (1 + u * (if t ∈ V then -1 else 1 : R)) = if t ∈ V then 1 - u else 1 + u := by
    intro t
    split_ifs <;> ring
  simp only [h]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hc : (Finset.univ.filter fun t => t ∉ V).card = 5 - V.card := by
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff]
    simp [Finset.inter_univ]
  rw [hc]
  ring

theorem sum_pattern {R : Type*} [CommRing R] (V : Finset (Fin 5)) :
    ∑ t, (if t ∈ V then -1 else 1 : R) = (5 : R) - 2 * V.card := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  have hc : (Finset.univ.filter fun t => t ∉ V).card = 5 - V.card := by
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff]
    simp [Finset.inter_univ]
  rw [hc, nsmul_eq_mul, nsmul_eq_mul]
  have hle : V.card ≤ 5 := by
    have := Finset.card_le_univ V
    simpa using this
  rw [Nat.cast_sub hle]
  push_cast
  ring

/-- The last-step direction's walk at a pattern `V`: `K_V = θ_V (𝐉 − I)`. -/
def patternK {R : Type*} [CommRing R] (V : Finset (Fin 5)) : Matrix (Fin 5) (Fin 5) R :=
  thetaP V * (Matrix.of fun i j : Fin 5 => if i = j then (0 : R) else 1)

/-- **Proposition 131 at every one of the 32 patterns:**
`(1 − u²) det(I − uK_V) = (1 + u)^a (1 − u)^d (1 + 4u² − u(a − d))`, `a = 5 − |V|`, `d = |V|`. -/
theorem pattern_factor {R : Type*} [CommRing R] (u : R) (V : Finset (Fin 5)) :
    (1 - u ^ 2) * (1 - u • patternK (R := R) V).det =
      (1 + u) ^ (5 - V.card) * (1 - u) ^ V.card * (1 + 4 * u ^ 2 - u * (5 - 2 * V.card)) := by
  have h := meeting_factor u (fun t => if t ∈ V then -1 else 1) (fun t => by split_ifs <;> ring)
  rw [prod_pattern, sum_pattern] at h
  rw [patternK, thetaP]
  exact h

/-- The polynomial form of `det(1 − u • M)` over `ℂ` (for the extension from `u² ≠ 1`). -/
theorem pattern_factor_cancelled (V : Finset (Fin 5)) (h1 : 1 ≤ V.card) (h4 : V.card ≤ 4)
    (u : ℂ) :
    (1 - u • patternK (R := ℂ) V).det =
      (1 + u) ^ (4 - V.card) * (1 - u) ^ (V.card - 1) * (1 + 4 * u ^ 2 - u * (5 - 2 * V.card)) := by
  revert u
  refine extend_from_generic (p := (1 - (Polynomial.X : Polynomial ℂ) •
      (patternK (R := ℂ) V).map Polynomial.C).det)
    (q := (1 + Polynomial.X) ^ (4 - V.card) * (1 - Polynomial.X) ^ (V.card - 1) *
      (1 + 4 * Polynomial.X ^ 2 - Polynomial.X * (5 - 2 * (V.card : Polynomial ℂ))))
    (det_one_sub_smul_poly _) (fun u => by simp) ?_
  intro u hu
  have h := pattern_factor u V
  have hp : (1 + u) ≠ 0 := by
    intro h0
    apply hu
    have : u = -1 := by linear_combination h0
    rw [this]
    norm_num
  have hm : (1 - u) ≠ 0 := by
    intro h0
    apply hu
    have : u = 1 := by linear_combination -h0
    rw [this]
    norm_num
  have e1 : (1 + u) ^ (5 - V.card) = (1 + u) * (1 + u) ^ (4 - V.card) := by
    rw [← pow_succ']
    congr 1
    omega
  have e2 : (1 - u) ^ V.card = (1 - u) * (1 - u) ^ (V.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [e1, e2] at h
  have hc : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  apply mul_left_cancel₀ hc
  linear_combination h

/-- **The singlet meeting:** `det(I − uK_∅) = (1 + u)⁴(1 − 4u)`. -/
theorem singlet_factor (u : ℂ) : (1 - u • patternK (R := ℂ) ∅).det = (1 + u) ^ 4 * (1 - 4 * u) := by
  revert u
  refine extend_from_generic (p := (1 - (Polynomial.X : Polynomial ℂ) •
      (patternK (R := ℂ) ∅).map Polynomial.C).det)
    (q := (1 + Polynomial.X) ^ 4 * (1 - 4 * Polynomial.X))
    (det_one_sub_smul_poly _) (fun u => by simp) ?_
  intro u hu
  have h := pattern_factor u (∅ : Finset (Fin 5))
  simp only [Finset.card_empty, Nat.sub_zero, pow_zero, mul_one, Nat.cast_zero, mul_zero,
    sub_zero] at h
  have hc : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  apply mul_left_cancel₀ hc
  linear_combination h

/-- **The counterpart of the singlet, all five lines divided:** `det(I − uK_{[5]}) = (1 − u)⁴(1 + 4u)`. -/
theorem all_factor (u : ℂ) :
    (1 - u • patternK (R := ℂ) Finset.univ).det = (1 - u) ^ 4 * (1 + 4 * u) := by
  revert u
  refine extend_from_generic (p := (1 - (Polynomial.X : Polynomial ℂ) •
      (patternK (R := ℂ) Finset.univ).map Polynomial.C).det)
    (q := (1 - Polynomial.X) ^ 4 * (1 + 4 * Polynomial.X))
    (det_one_sub_smul_poly _) (fun u => by simp) ?_
  intro u hu
  have h := pattern_factor u (Finset.univ : Finset (Fin 5))
  simp only [Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, one_mul] at h
  have hc : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  apply mul_left_cancel₀ hc
  linear_combination h

/-- **`Σ_U (a_U − 1) = Σ_U (d_U − 1) = 24`** over the sixteen meetings. -/
theorem sum_agree_minus_one :
    (∑ U : Fin 16, ((5 - (disagreeSet U).card : ℤ) - 1)) = 24 ∧
      (∑ U : Fin 16, (((disagreeSet U).card : ℤ) - 1)) = 24 := by
  decide

/-! ## The sixteen meetings multiply to the law -/

section Product

variable {K : Type*} [Field K] [CharZero K]

/-- The meetings' blocks are a block-diagonal matrix with the meeting outside. -/
theorem meetBlocks_eq_submatrix (M : Fin 16 → Matrix (Fin 5) (Fin 5) K) :
    meetBlocks K M = (blockDiagonal M).submatrix (Equiv.prodComm (Fin 16) (Fin 5))
      (Equiv.prodComm (Fin 16) (Fin 5)) := by
  ext ⟨U, a⟩ ⟨V, b⟩
  simp only [meetBlocks, Matrix.of_apply, Matrix.submatrix_apply, Equiv.prodComm_apply,
    Prod.fst_swap, Prod.snd_swap, blockDiagonal_apply]

/-- **`det ⊕_U M_U = ∏_U det M_U`.** -/
theorem det_meetBlocks (M : Fin 16 → Matrix (Fin 5) (Fin 5) K) :
    (meetBlocks K M).det = ∏ U, (M U).det := by
  rw [meetBlocks_eq_submatrix, det_submatrix_equiv_self, det_blockDiagonal]

theorem one_sub_meetBlocks (u : K) (M : Fin 16 → Matrix (Fin 5) (Fin 5) K) :
    1 - u • meetBlocks K M = meetBlocks K (fun U => 1 - u • M U) := by
  ext ⟨U, a⟩ ⟨V, b⟩
  simp only [meetBlocks, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Prod.mk.injEq, smul_eq_mul]
  by_cases h : U = V
  · subst h
    simp
  · simp [h]

theorem det_conj_charX80 (M : Matrix State State K) :
    (charX80 K * M * charX80 K).det = M.det := by
  rw [det_mul, det_mul]
  have h := det_charX80_sq (K := K)
  linear_combination M.det * h

end Product

theorem stepOp_transitionMat_eq : stepOp transitionMat = transitionShaped ℂ (fun a b => if a = b then 0 else 1) := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [stepOp, transitionShaped, transitionMat, transitionMatZ, Matrix.of_apply, Matrix.map_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · by_cases hx : x = transition a y <;> simp [hab, hx]

theorem patternK_disagree (U : Fin 16) :
    thetaM ℂ U * Matrix.of (fun a b : Fin 5 => if a = b then (0 : ℂ) else 1) =
      patternK (disagreeSet U) := by
  rw [patternK]
  congr 1
  ext a b
  simp only [thetaM, thetaP, diagonal_apply, agreeSign, charSign]
  split_ifs <;> simp

/-- **The sixteen meetings multiply to the law:** `∏_U det(I − uK_U) = det(I − uB)`. -/
theorem law_meetings (u : ℂ) :
    ∏ U : Fin 16, (1 - u • patternK (R := ℂ) (disagreeSet U)).det =
      (1 - u • stepOp transitionMat).det := by
  rw [← det_conj_charX80 (K := ℂ), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    charX80_mul_self, Matrix.mul_smul, Matrix.smul_mul, stepOp_transitionMat_eq, conj_transitionShaped,
    one_sub_meetBlocks, det_meetBlocks]
  simp only [patternK_disagree]

/-- **The sixteen counterparts multiply to `det(I + uB)`:** a counterpart's block is `−K_U`. -/
theorem law_twins (u : ℂ) :
    ∏ U : Fin 16, (1 - u • patternK (R := ℂ) (disagreeSet U)ᶜ).det =
      (1 + u • stepOp transitionMat).det := by
  have h : ∀ U : Fin 16, patternK (R := ℂ) (disagreeSet U)ᶜ = -patternK (disagreeSet U) := by
    intro U
    rw [patternK, patternK, thetaP_compl, Matrix.neg_mul]
  simp only [h, smul_neg, sub_neg_eq_add]
  have := law_meetings (-u)
  simp only [neg_smul, sub_neg_eq_add] at this
  exact this

/-- **With Proposition 54:** `∏_U det(I − uK_U) = (1 − u²)²⁴ ∏_U (1 + 4u² − uλ_U)`,
`λ_U = 5 − 2|T_U|`. -/
theorem law_meetings_closed (u : ℂ) :
    ∏ U : Fin 16, (1 - u • patternK (R := ℂ) (disagreeSet U)).det =
      (1 - u ^ 2) ^ 24 * ∏ U : Fin 16, (1 + 4 * u ^ 2 - u * (5 - 2 * (disagreeSet U).card)) := by
  rw [law_meetings, D_plus]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  simp [disagreeSet]
  ring

end Law

end Comparison

end
