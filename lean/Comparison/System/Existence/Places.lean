import Comparison.System.Existence.Line
import Comparison.System.Existence.Ext.Commutant
import Comparison.System.Existence.Ext.JointStep
import Comparison.System.Existence.Ext.EvenFour
import Comparison.Existence.CovDiff
import Comparison.Existence.PlaquetteData
import Comparison.Article.Holonomy
import Comparison.Article.Splits
import Comparison.Article.Whole
import Comparison.Article.Geometry3
import Comparison.ArticleStatements.CommonClock

/-!
# The proof system, the existence layer: at every vertex, in both directions (Propositions 32 to 39, 91)

Book VII: closed facts (Prop. 32), the vertical step (Prop. 33),
spin one half (Prop. 34), the phase of the whole (Prop. 35), the parallel rotation (Prop. 36), one step joins the two
(Prop. 37), curvature (Prop. 38), the mass form (Prop. 39), and the common clock (Prop. 91). The exterior algebra of
the six is the copy `System/Existence/Ext/` (namespace `Comparison.SysExt`).
-/

namespace Comparison.System.Existence

open Matrix Complex Kronecker

/-! ## Proposition 32 -/

/-- The trivial connection. -/
def trivialConnection (X G : Type*) [Group G] : Connection X G := ⟨fun _ _ => 1, fun _ _ => by simp⟩

/-- **Proposition 32 (closed facts).** A gauge transformation takes `U_xy ↦ g_xU_xyg_y⁻¹`; the holonomy of a closed walk
at `x₀` turns by the gauge at its own vertex, `hol ↦ g_{x₀} hol g_{x₀}⁻¹`, so its trace is a fact; the transport of an
open walk from `x` to `y ≠ x` can be gauge-transformed into every rotation, and only the constants are facts of it.

Recognition: Einstein's point coincidences and the gauge principle, with Wilson's closed loops. Uses P4,
Definition 24. -/
theorem prop_32 {X G : Type*} [Group G] :
    (∀ (c : Connection X G) (g : X → G) (x y : X), (c.rename g).U x y = g x * c.U x y * (g y)⁻¹) ∧
    (∀ (c : Connection X G) (g : X → G) (x : X) (rest : List X),
      (x :: rest).getLast (List.cons_ne_nil x rest) = x →
      hol (c.rename g) (x :: rest) = g x * hol c (x :: rest) * (g x)⁻¹) ∧
    (∀ (c : Connection X G) (x : X) (rest : List X),
      (x :: rest).getLast (List.cons_ne_nil x rest) ≠ x →
      ∀ V : G, ∃ g : X → G, hol (c.rename g) (x :: rest) = V) ∧
    (∀ {α : Type*} (φ : G → α) (x : X) (rest : List X),
      (x :: rest).getLast (List.cons_ne_nil x rest) ≠ x →
      IsFact (fun c : Connection X G => φ (hol c (x :: rest))) → ∀ V W : G, φ V = φ W) := by
  have hopen : ∀ (c : Connection X G) (x : X) (rest : List X),
      (x :: rest).getLast (List.cons_ne_nil x rest) ≠ x →
      ∀ V : G, ∃ g : X → G, hol (c.rename g) (x :: rest) = V := by
    classical
    intro c x rest hne V
    set y := (x :: rest).getLast (List.cons_ne_nil x rest) with hy
    refine ⟨Function.update (fun _ => 1) y (V * (hol c (x :: rest))⁻¹), ?_⟩
    rw [hol_rename, ← hy, Function.update_self, Function.update_of_ne (Ne.symm hne)]
    simp
  refine ⟨fun c g x y => rfl, fun c g x rest h => hol_rename_closed c g x rest h, hopen, ?_⟩
  intro α φ x rest hne hfact V W
  obtain ⟨g, hg⟩ := hopen (trivialConnection X G) x rest hne V
  obtain ⟨g', hg'⟩ := hopen (trivialConnection X G) x rest hne W
  have h1 := hfact (trivialConnection X G) g
  have h2 := hfact (trivialConnection X G) g'
  simp only at h1 h2
  rw [hg] at h1
  rw [hg'] at h2
  rw [h1, h2]

/-- The trace of the holonomy of a closed walk, for every group of invertible matrices: a fact (P4). -/
theorem prop_32_trace {X : Type*} {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] (x : X)
    (rest : List X) (hclosed : (x :: rest).getLast (List.cons_ne_nil x rest) = x) :
    IsFact (fun c : Connection X (Matrix n n R)ˣ =>
      ((hol c (x :: rest) : (Matrix n n R)ˣ) : Matrix n n R).trace) :=
  trace_hol_closed_isFact x rest hclosed

/-! ## Proposition 33 -/

/-- **Proposition 33 (the vertical step).** On the exterior algebra of `n` directions (the sixty-four sets at `n = 6`):
`ι(v)ε(w) + ε(w)ι(v) = ⟨v, w⟩`, `ε(v)ε(w) + ε(w)ε(v) = 0 = ι(v)ι(w) + ι(w)ι(v)`; `J(v) = ε(v) + ι(v)` has
`J(v)J(w) + J(w)J(v) = 2⟨v, w⟩` and `J(v)² = |v|²`; `J_a f_S = (−1)^{#\{s ∈ S : s < a\}} f_{S △ \{a\}}`;
`J_{s₁} ⋯ J_{s_r} f_∅ = f_{\{s₁,…,s_r\}}` (`s₁ < ⋯ < s_r`); `Λ(O) J(v) Λ(O)⁻¹ = J(Ov)` for every rotation `O`
(`Λ(O)⁻¹ = Λ(Oᵀ)`); and the step of the proof: the whole `w = J₀⋯J₅` turns adding into removing,
`w ε_a = −ι_a w`.

Recognition: dividing a direction and undividing it are one operation. Uses Definitions 13, 26, P3 (b). -/
theorem prop_33 {n : ℕ} {R : Type*} [CommRing R] :
    (∀ v w : Fin n → R, SysExt.ιv v * SysExt.εv w + SysExt.εv w * SysExt.ιv v =
      (v ⬝ᵥ w) • (1 : Module.End R (Finset (Fin n) → R))) ∧
    (∀ v w : Fin n → R, SysExt.εv v * SysExt.εv w + SysExt.εv w * SysExt.εv v = 0) ∧
    (∀ v w : Fin n → R, SysExt.ιv v * SysExt.ιv w + SysExt.ιv w * SysExt.ιv v = 0) ∧
    (∀ v w : Fin n → R, SysExt.Jv v * SysExt.Jv w + SysExt.Jv w * SysExt.Jv v =
      (2 * (v ⬝ᵥ w)) • (1 : Module.End R (Finset (Fin n) → R))) ∧
    (∀ v : Fin n → R, SysExt.Jv v * SysExt.Jv v = (v ⬝ᵥ v) • (1 : Module.End R (Finset (Fin n) → R))) ∧
    (∀ (a : Fin n) (S : Finset (Fin n)), SysExt.Jx (R := R) a (Pi.single S (1 : R)) =
      SysExt.extSign (R := R) a (S.erase a) • (Pi.single (symmDiff S {a}) (1 : R) : Finset (Fin n) → R)) ∧
    (∀ S : Finset (Fin n), SysExt.ordProd (SysExt.Jx (R := R)) S (Pi.single ∅ 1) = Pi.single S 1) ∧
    (∀ (O : Matrix (Fin n) (Fin n) R), Oᵀ * O = 1 →
      SysExt.extMap O * SysExt.extMap Oᵀ = 1 ∧ SysExt.extMap Oᵀ * SysExt.extMap O = 1 ∧
      ∀ v : Fin n → R, SysExt.extMap O * SysExt.Jv v * SysExt.extMap Oᵀ = SysExt.Jv (O *ᵥ v)) ∧
    (∀ a : Fin 6, Article.whole (A := Module.End ℂ (Finset (Fin 6) → ℂ)) (fun a => SysExt.εx a)
        (fun a => SysExt.ιx a) * SysExt.εx a =
      -(SysExt.ιx a * Article.whole (A := Module.End ℂ (Finset (Fin 6) → ℂ)) (fun a => SysExt.εx a)
        (fun a => SysExt.ιx a))) := by
  refine ⟨SysExt.ιv_εv_add, SysExt.εv_anticomm, SysExt.ιv_anticomm, SysExt.Jv_anticomm, SysExt.Jv_mul_self,
    SysExt.Jx_single, SysExt.ordProd_Jx_vac, fun O hO => ⟨(SysExt.extMap_mul_transpose O hO).1,
      (SysExt.extMap_mul_transpose O hO).2, SysExt.extMap_conj_Jv O hO⟩, fun a => ?_⟩
  exact Article.whole_turns_adding _ _ (fun a b => SysExt.εx_εx_add a b) (fun a b => SysExt.ιx_ιx_add a b)
    (fun a b => SysExt.εx_ιx_add a b) a

/-- The whole of the article's theorem is the product of the six vertical steps. -/
theorem whole_eq_volume :
    Article.whole (A := Module.End ℂ (Finset (Fin 6) → ℂ)) (fun a => SysExt.εx a) (fun a => SysExt.ιx a) =
      SysExt.Jx 0 * SysExt.Jx 1 * SysExt.Jx 2 * SysExt.Jx 3 * SysExt.Jx 4 * SysExt.Jx 5 := rfl

/-! ## Proposition 34 -/

/-- **In a complete normed real algebra, `X² = −1` gives `e^{θX} = cos θ + sin θ X`.** -/
theorem exp_smul_of_sq_neg {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (X : 𝔸) (hX : X * X = -1) (θ : ℝ) :
    NormedSpace.exp (θ • X) = Real.cos θ • (1 : 𝔸) + Real.sin θ • X := by
  have heven : ∀ k : ℕ, X ^ (2 * k) = ((-1 : ℝ) ^ k) • (1 : 𝔸) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, ih, pow_two, hX, pow_succ, smul_mul_assoc,
        one_mul, mul_neg_one, neg_smul, smul_neg]
  have hodd : ∀ k : ℕ, X ^ (2 * k + 1) = ((-1 : ℝ) ^ k) • X := by
    intro k
    rw [pow_succ, heven k, smul_mul_assoc, one_mul]
  rw [NormedSpace.exp_eq_tsum ℝ]
  refine HasSum.tsum_eq ?_
  set f : ℕ → 𝔸 := fun n => ((n.factorial : ℝ)⁻¹) • (θ • X) ^ n with hf
  have hc := (Real.hasSum_cos θ).smul_const (1 : 𝔸)
  have hs := (Real.hasSum_sin θ).smul_const X
  have he : HasSum (fun k => f (2 * k)) (Real.cos θ • (1 : 𝔸)) := by
    convert hc using 1
    funext k
    simp only [hf]
    rw [smul_pow, heven k, smul_smul, smul_smul]
    congr 1
    ring
  have ho : HasSum (fun k => f (2 * k + 1)) (Real.sin θ • X) := by
    convert hs using 1
    funext k
    simp only [hf]
    rw [smul_pow, hodd k, smul_smul, smul_smul]
    congr 1
    ring
  exact he.even_add_odd ho

set_option backward.isDefEq.respectTransparency false in
/-- `e^{θM} = cos θ + sin θ M` for a real matrix with `M² = −1`. -/
theorem matrix_exp_smul_of_sq_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hM : M * M = -1) (θ : ℝ) :
    NormedSpace.exp (θ • M) = Real.cos θ • (1 : Matrix ι ι ℝ) + Real.sin θ • M :=
  open scoped Matrix.Norms.Operator in exp_smul_of_sq_neg M hM θ

theorem JJ_sq {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    (SysExt.Jx (R := ℝ) a * SysExt.Jx b) * (SysExt.Jx a * SysExt.Jx b) = -1 := by
  rw [show SysExt.Jx (R := ℝ) a * SysExt.Jx b * (SysExt.Jx a * SysExt.Jx b) =
    SysExt.Jx a * SysExt.Jx b * SysExt.Jx a * SysExt.Jx b by noncomm_ring, SysExt.shortest_loop hab]

/-- **The rotor is the exponential:** `R_ab(ϑ) = e^{ϑJ_aJ_b/2}`, as matrices on the sets. -/
theorem rotor_eq_exp {n : ℕ} {a b : Fin n} (hab : a ≠ b) (θ : ℝ) :
    NormedSpace.exp ((θ / 2) • LinearMap.toMatrixAlgEquiv' (SysExt.Jx (R := ℝ) a * SysExt.Jx b)) =
      LinearMap.toMatrixAlgEquiv' (SysExt.rotor a b θ) := by
  have hsq : LinearMap.toMatrixAlgEquiv' (SysExt.Jx (R := ℝ) a * SysExt.Jx b) *
      LinearMap.toMatrixAlgEquiv' (SysExt.Jx (R := ℝ) a * SysExt.Jx b) = -1 := by
    rw [← map_mul, JJ_sq hab, map_neg, map_one]
  rw [matrix_exp_smul_of_sq_neg _ hsq, SysExt.rotor, map_add, map_smul, map_smul, map_one]

theorem Jv_eq_sum {n : ℕ} {R : Type*} [CommRing R] (v : Fin n → R) :
    SysExt.Jv v = ∑ c, v c • SysExt.Jx c := by
  conv_lhs => rw [SysExt.vec_eq_sum v]
  simp only [SysExt.Jv, SysExt.εv_sum, SysExt.ιv_sum, SysExt.εv_smul, SysExt.ιv_smul, SysExt.εv_single,
    SysExt.ιv_single, ← Finset.sum_add_distrib, ← smul_add]
  rfl

theorem Jv_single {n : ℕ} {R : Type*} [CommRing R] (a : Fin n) :
    SysExt.Jv (R := R) (Pi.single a 1) = SysExt.Jx a := by
  simp only [SysExt.Jv, SysExt.εv_single, SysExt.ιv_single]
  rfl

theorem Jv_add' {n : ℕ} {R : Type*} [CommRing R] (u w : Fin n → R) :
    SysExt.Jv (u + w) = SysExt.Jv u + SysExt.Jv w := by
  simp only [SysExt.Jv, SysExt.εv_add, SysExt.ιv_add]
  abel

theorem Jv_smul' {n : ℕ} {R : Type*} [CommRing R] (c : R) (u : Fin n → R) :
    SysExt.Jv (c • u) = c • SysExt.Jv u := by
  simp only [SysExt.Jv, SysExt.εv_smul, SysExt.ιv_smul, smul_add]

theorem Jv_sub' {n : ℕ} {R : Type*} [CommRing R] (u w : Fin n → R) :
    SysExt.Jv (u - w) = SysExt.Jv u - SysExt.Jv w := by
  have hneg : SysExt.Jv (-w) = -SysExt.Jv w := by
    rw [show -w = (-1 : R) • w by simp, Jv_smul', neg_one_smul]
  rw [sub_eq_add_neg, Jv_add', hneg, ← sub_eq_add_neg]

theorem rotor_comm_other {n : ℕ} {a b c : Fin n} (hca : c ≠ a) (hcb : c ≠ b) (θ : ℝ) :
    SysExt.rotor a b θ * SysExt.Jx c = SysExt.Jx c * SysExt.rotor a b θ := by
  have h : (SysExt.Jx (R := ℝ) a * SysExt.Jx b) * SysExt.Jx c =
      SysExt.Jx c * (SysExt.Jx a * SysExt.Jx b) := by
    have h1 : SysExt.Jx (R := ℝ) b * SysExt.Jx c = -(SysExt.Jx c * SysExt.Jx b) :=
      SysExt.Jx_anticomm (Ne.symm hcb)
    have h2 : SysExt.Jx (R := ℝ) a * SysExt.Jx c = -(SysExt.Jx c * SysExt.Jx a) :=
      SysExt.Jx_anticomm (Ne.symm hca)
    calc (SysExt.Jx (R := ℝ) a * SysExt.Jx b) * SysExt.Jx c
        = SysExt.Jx a * (SysExt.Jx b * SysExt.Jx c) := by rw [mul_assoc]
      _ = -((SysExt.Jx a * SysExt.Jx c) * SysExt.Jx b) := by rw [h1, mul_neg, ← mul_assoc]
      _ = SysExt.Jx c * (SysExt.Jx a * SysExt.Jx b) := by rw [h2, neg_mul, neg_neg, mul_assoc]
  simp only [SysExt.rotor, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h]

/-- **The step turns its plane:** `R_ab(ϑ) J(v) R_ab(ϑ)⁻¹ = J(O_ϑ v)` for every direction `v`. -/
theorem rotor_conj_Jv {n : ℕ} {a b : Fin n} (hab : a ≠ b) (θ : ℝ) (v : Fin n → ℝ) :
    SysExt.rotor a b θ * SysExt.Jv v * SysExt.rotor a b (-θ) =
      SysExt.Jv (SysExt.planeRot a b θ *ᵥ v) := by
  have hinv : SysExt.rotor a b θ * SysExt.rotor a b (-θ) = 1 := by
    rw [SysExt.rotor_mul hab, add_neg_cancel, SysExt.rotor_zero]
  have hcol : ∀ c : Fin n, SysExt.rotor a b θ * SysExt.Jx c * SysExt.rotor a b (-θ) =
      SysExt.Jv ((SysExt.planeRot a b θ).col c) := by
    intro c
    by_cases hca : c = a
    · subst hca
      rw [SysExt.rotor_conj_a hab, SysExt.planeRot_col_a hab, Jv_sub', Jv_smul', Jv_smul', Jv_single,
        Jv_single]
    · by_cases hcb : c = b
      · subst hcb
        rw [SysExt.rotor_conj_b hab, SysExt.planeRot_col_b hab, Jv_add', Jv_smul', Jv_smul',
          Jv_single, Jv_single]
      · rw [rotor_comm_other hca hcb, mul_assoc, hinv, mul_one, SysExt.planeRot_col_other hab hca hcb,
          Jv_single]
  have hO : SysExt.planeRot a b θ *ᵥ v = ∑ c, v c • (SysExt.planeRot a b θ).col c :=
    SysExt.mulVec_eq_sum_col _ v
  have hJsum : ∀ (s : Finset (Fin n)) (u : Fin n → Fin n → ℝ),
      SysExt.Jv (∑ c ∈ s, u c) = ∑ c ∈ s, SysExt.Jv (u c) := by
    intro s u
    simp only [SysExt.Jv, SysExt.εv_sum, SysExt.ιv_sum, ← Finset.sum_add_distrib]
  conv_lhs => rw [Jv_eq_sum]
  rw [hO, hJsum]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, Jv_smul', hcol]

theorem planeRot_two_pi {n : ℕ} (a b : Fin n) : SysExt.planeRot a b (2 * Real.pi) = 1 := by
  simp [SysExt.planeRot]

/-- **Proposition 34 (spin one half).** `J_aJ_bJ_aJ_b = −1` (`a ≠ b`): the loop `f_∅ → f_b → f_{ab} → f_a → f_∅`
comes back with `−1`; `R_ab(ϑ) = e^{ϑJ_aJ_b/2} = cos(ϑ/2) + J_aJ_b sin(ϑ/2)`, `R_ab(ϑ) J(v) R_ab(ϑ)⁻¹ = J(O_ϑ v)`
for every `v` (`O_ϑ` the rotation of the plane `(a, b)` by `ϑ`), and `R_ab(2π) = −1` while `O_{2π} = 1`; with the square
root of the sign of a division `D`, `f_x = i^{[x ∈ D]} J_x` has `f_xf_y + f_yf_x = 2θ_D(x)δ_xy` and
`(f_xf_y)² = −θ_D(x)θ_D(y)` (`x ≠ y`): `−1` on the `C(k,2) + C(6−k,2)` planes within a side and `+1` on the
`k(6−k)` planes across (`k = |D|`).

Recognition: spin one half, four quarter turns around a plane come back with `−1`; a loop across the division is a
boost and never closes. Uses Props. 21, 33, Definition 14. -/
theorem prop_34 {n : ℕ} :
    (∀ a b : Fin n, a ≠ b → SysExt.Jx (R := ℝ) a * SysExt.Jx b * SysExt.Jx a * SysExt.Jx b = -1) ∧
    (∀ a b : Fin n, a ≠ b →
      SysExt.Jx (R := ℝ) a (SysExt.Jx b (SysExt.Jx a (SysExt.Jx b (Pi.single (∅ : Finset (Fin n)) 1)))) =
        -Pi.single (∅ : Finset (Fin n)) (1 : ℝ)) ∧
    (∀ a b : Fin n, a ≠ b → ∀ θ : ℝ,
      NormedSpace.exp ((θ / 2) • LinearMap.toMatrixAlgEquiv' (SysExt.Jx (R := ℝ) a * SysExt.Jx b)) =
        LinearMap.toMatrixAlgEquiv' (SysExt.rotor a b θ) ∧
      SysExt.rotor a b θ = Real.cos (θ / 2) • 1 + Real.sin (θ / 2) • (SysExt.Jx a * SysExt.Jx b)) ∧
    (∀ a b : Fin n, a ≠ b → ∀ θ : ℝ, SysExt.rotor a b θ * SysExt.rotor a b (-θ) = 1 ∧
      ∀ v : Fin n → ℝ, SysExt.rotor a b θ * SysExt.Jv v * SysExt.rotor a b (-θ) =
        SysExt.Jv (SysExt.planeRot a b θ *ᵥ v)) ∧
    (∀ a b : Fin n, SysExt.rotor a b (2 * Real.pi) = -1 ∧ SysExt.planeRot a b (2 * Real.pi) = 1) ∧
    (∀ (D : Finset (Fin 6)) (x y : Fin 6),
      SysExt.halfStep D x * SysExt.halfStep D y + SysExt.halfStep D y * SysExt.halfStep D x =
        if x = y then (2 * thetaAt D x) • 1 else 0) ∧
    (∀ (D : Finset (Fin 6)) (x y : Fin 6), x ≠ y →
      (SysExt.halfStep D x * SysExt.halfStep D y) * (SysExt.halfStep D x * SysExt.halfStep D y) =
        (-(thetaAt D x * thetaAt D y)) • 1) ∧
    (∀ D : Finset (Fin 6),
      (Finset.univ.filter fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ (p.1 ∈ D ↔ p.2 ∈ D)).card =
        D.card.choose 2 + (6 - D.card).choose 2 ∧
      (Finset.univ.filter fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ ¬(p.1 ∈ D ↔ p.2 ∈ D)).card =
        D.card * (6 - D.card)) := by
  refine ⟨fun a b hab => SysExt.shortest_loop hab, fun a b hab => by
      have h := LinearMap.congr_fun (SysExt.shortest_loop (R := ℝ) hab) (Pi.single ∅ 1)
      simpa only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply] using h,
    fun a b hab θ => ⟨rotor_eq_exp hab θ, rfl⟩, fun a b hab θ => ⟨?_, rotor_conj_Jv hab θ⟩,
    fun a b => ⟨SysExt.rotor_two_pi a b, planeRot_two_pi a b⟩, fun D x y => ?_, fun D x y hxy => ?_,
    SysExt.loop_counts⟩
  · rw [SysExt.rotor_mul hab, add_neg_cancel, SysExt.rotor_zero]
  · rw [SysExt.half_anticomm]
    simp only [thetaAt]
  · rw [SysExt.half_loop_sq D hxy]
    simp only [thetaAt]

/-! ## Proposition 35 -/

/-- An ordered product of scaled steps: `∏ (c_a E_a) = (∏ c_a) ∏ E_a`. -/
theorem list_prod_map_smul {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {ι : Type*}
    (l : List ι) (c : ι → R) (E : ι → A) :
    (l.map fun a => c a • E a).prod = (l.map c).prod • (l.map E).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.map_cons, List.prod_cons,
      List.prod_cons, smul_mul_smul_comm]

theorem ordProd_smul {n : ℕ} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (c : Fin n → R) (E : Fin n → A) (S : Finset (Fin n)) :
    SysExt.ordProd (fun a => c a • E a) S = (∏ a ∈ S, c a) • SysExt.ordProd E S := by
  rw [SysExt.ordProd, SysExt.ordProd, list_prod_map_smul]
  congr 1
  rw [← List.prod_toFinset c (Finset.sort_nodup S (· ≤ ·)), Finset.sort_toFinset]

/-- **`Λ` of a diagonal matrix:** `Λ(diag d) f_S = (∏_{s ∈ S} d_s) f_S`. -/
theorem extMap_diagonal {n : ℕ} {R : Type*} [CommRing R] (d : Fin n → R) (S : Finset (Fin n)) :
    SysExt.extMap (Matrix.diagonal d) (Pi.single S 1) = (∏ s ∈ S, d s) • Pi.single S 1 := by
  have hcol : ∀ a, SysExt.colStep (Matrix.diagonal d) a = d a • SysExt.εx a := by
    intro a
    rw [SysExt.colStep]
    have : (Matrix.diagonal d).col a = d a • (Pi.single a 1 : Fin n → R) := by
      funext i
      simp only [Matrix.col_apply, Matrix.diagonal_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs with h
      · subst h; simp
      · simp
    rw [this, SysExt.εv_smul, SysExt.εv_single]
  rw [SysExt.extMap_single]
  have hfun : SysExt.colStep (Matrix.diagonal d) = fun a => d a • SysExt.εx a := funext hcol
  rw [hfun, ordProd_smul, LinearMap.smul_apply, SysExt.ordProd_εx_vac]

theorem det_theta (S : Finset (Fin 6)) : (theta ℂ S).det = (-1) ^ S.card := by
  rw [theta, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem det_half (D : Finset (Fin 6)) : (half D).det = Complex.I ^ D.card := by
  rw [half, Matrix.det_diagonal, half_on_sets, Finset.univ_inter]

/-- **Proposition 35 (the phase of the whole).** `w = J₀J₁⋯J₅` has `w² = −1`; with the square root of the sign of `D`,
`f₀f₁⋯f₅ = i^{|D|} w`; `Λ(q_D) f_{\{0,…,5\}} = det(q_D) f_{\{0,…,5\}} = i^{|D|} f_{\{0,…,5\}}`;
`Λ(iI) f_S = i^{|S|} f_S`, `z_S = i^{|S|}`; `z_S² = det θ_S = (−1)^{|S|}`; `z_S = 1, i, −1, i, −1, −i` on the six
divided sets `{}, {n}, {h,n}, {h}, F, C` of a line; and `z_{S △ \{n\}} = ±i z_S`.

Recognition: the four phases `1, i, −1, −i`; counterparts differ by a quarter turn. Uses Props. 19, 27, 33, 34. -/
theorem prop_35 :
    SysExt.volume (R := ℂ) * SysExt.volume = -1 ∧
    (∀ D : Finset (Fin 6), (List.ofFn (SysExt.halfStep D)).prod = Complex.I ^ D.card • SysExt.volume) ∧
    (∀ D : Finset (Fin 6), SysExt.extMap (half D) (Pi.single Finset.univ 1) =
        (half D).det • Pi.single Finset.univ 1 ∧ (half D).det = Complex.I ^ D.card) ∧
    (∀ S : Finset (Fin 6), SysExt.extMap (Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) (Pi.single S 1) =
      Complex.I ^ S.card • Pi.single S 1 ∧ zS S = Complex.I ^ S.card) ∧
    (∀ S : Finset (Fin 6), zS S ^ 2 = (theta ℂ S).det ∧ (theta ℂ S).det = (-1) ^ S.card) ∧
    (∀ h k : Fin 5, h ≠ k → zS ∅ = 1 ∧ zS {0} = Complex.I ∧ zS {0, h.succ} = -1 ∧
      zS {h.succ} = Complex.I ∧ zS {h.succ, k.succ} = -1 ∧
      zS ((({h, k} : Finset (Fin 5))ᶜ).map (Fin.succEmb 5)) = -Complex.I) ∧
    (∀ S : Finset (Fin 6), zS (symmDiff S {0}) = Complex.I * zS S ∨
      zS (symmDiff S {0}) = -Complex.I * zS S) := by
  have hz : ∀ S : Finset (Fin 6), zS S = Complex.I ^ S.card := fun S => rfl
  refine ⟨SysExt.volume_sq, SysExt.half_prod, fun D => ⟨?_, det_half D⟩, fun S => ⟨?_, rfl⟩,
    fun S => ⟨?_, det_theta S⟩, fun h k hk => ?_, fun S => ?_⟩
  · rw [half, extMap_diagonal, ← Matrix.det_diagonal]
  · rw [Matrix.smul_one_eq_diagonal, extMap_diagonal, Finset.prod_const]
  · rw [det_theta, hz, ← pow_mul, mul_comm, pow_mul, Complex.I_sq]
  · have hc : ∀ h k : Fin 5, h ≠ k → ({0, h.succ} : Finset (Fin 6)).card = 2 ∧
        ({h.succ, k.succ} : Finset (Fin 6)).card = 2 ∧
        ((({h, k} : Finset (Fin 5))ᶜ).map (Fin.succEmb 5)).card = 3 := by decide
    obtain ⟨c1, c2, c3⟩ := hc h k hk
    refine ⟨by simp [hz], by simp [hz], by simp [hz, c1], by simp [hz], by simp [hz, c2], ?_⟩
    rw [hz, c3, pow_succ, Complex.I_sq]
    ring
  · by_cases h0 : (0 : Fin 6) ∈ S
    · right
      have hsd : symmDiff S {0} = S.erase 0 := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
        constructor
        · rintro (⟨hx, hx0⟩ | ⟨rfl, hx⟩)
          · exact ⟨hx0, hx⟩
          · exact absurd h0 hx
        · rintro ⟨hx0, hx⟩
          exact Or.inl ⟨hx, hx0⟩
      rw [hsd, hz, hz]
      have hcard := Finset.card_erase_add_one h0
      rw [← hcard, pow_succ]
      linear_combination (Complex.I ^ (S.erase 0).card) * Complex.I_sq
    · left
      have hsd : symmDiff S {0} = insert 0 S := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
        constructor
        · rintro (⟨hx, -⟩ | ⟨rfl, -⟩)
          · exact Or.inr hx
          · exact Or.inl rfl
        · rintro (rfl | hx)
          · exact Or.inr ⟨rfl, h0⟩
          · exact Or.inl ⟨hx, fun h => h0 (h ▸ hx)⟩
      rw [hsd, hz, hz, Finset.card_insert_of_notMem h0, pow_succ, mul_comm]

/-! ## Proposition 36 -/

/-- **Proposition 36 (the parallel rotation).** `T_ab = ε_aι_b − ε_bι_a = Σ_k Π_kJ_aJ_bΠ_k` (`a ≠ b`); `NT_ab = T_abN`;
`T_abT_bc − T_bcT_ab = T_ac` (`a, b, c` distinct) and `T_abT_cd = T_cdT_ab` (`{a,b} ∩ {c,d} = ∅`);
`J_aJ_b = T_ab + ε_aε_b + ι_aι_b` (`a ≠ b`); `e^{ϑT_ab} = Λ(e^{ϑ(E_ab − E_ba)})`.

Recognition: the parallel rotation is already inside the vertical square; the fifteen rotations of the six act on every
division at once. Uses Props. 17, 33, Definition 26. -/
theorem prop_36 {n : ℕ} {R : Type*} [CommRing R] :
    (∀ a b : Fin n, a ≠ b → SysExt.Tx (R := R) a b =
      ∑ k ∈ Finset.range (n + 1), SysExt.degreeProj k * (SysExt.Jx a * SysExt.Jx b) * SysExt.degreeProj k) ∧
    (∀ a b : Fin n, SysExt.Nx * SysExt.Tx (R := R) a b = SysExt.Tx a b * SysExt.Nx) ∧
    (∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c →
      SysExt.Tx (R := R) a b * SysExt.Tx b c - SysExt.Tx b c * SysExt.Tx a b = SysExt.Tx a c) ∧
    (∀ a b c d : Fin n, a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      SysExt.Tx (R := R) a b * SysExt.Tx c d = SysExt.Tx c d * SysExt.Tx a b) ∧
    (∀ a b : Fin n, a ≠ b →
      SysExt.Jx (R := R) a * SysExt.Jx b = SysExt.Tx a b + SysExt.εx a * SysExt.εx b + SysExt.ιx a * SysExt.ιx b) ∧
    (∀ a b : Fin n, a ≠ b → ∀ θ : ℝ,
      NormedSpace.exp (θ • LinearMap.toMatrixAlgEquiv' (SysExt.Tx (R := ℝ) a b)) =
        LinearMap.toMatrixAlgEquiv' (SysExt.extMap (NormedSpace.exp (θ • unitTurn a b)))) :=
  ⟨fun a b hab => SysExt.Tx_eq_sum_degrees hab, SysExt.Nx_Tx,
    fun a b c hab hbc hac => SysExt.Tx_comm_chain hab hbc hac,
    fun a b c d hac had hbc hbd => sub_eq_zero.mp (SysExt.Tx_comm_disjoint hac had hbc hbd),
    fun a b hab => SysExt.Jx_mul_Jx hab, fun a b hab θ => SysExt.exp_parallel_turn hab θ⟩

/-! ## Proposition 37 -/

/-- The whole `w = J₀J₁⋯J₅` as an even word: `(J_nJ_1)(J_2J_3)(J_4J_5)` in the lines' numbering. -/
noncomputable def wholeEven : CliffordAlgebra.even SysExt.Q6 :=
  SysExt.singletLine 0 * SysExt.lineLine 1 2 * SysExt.lineLine 3 4

theorem wholeEven_val :
    (wholeEven : CliffordAlgebra SysExt.Q6) =
      SysExt.cl 0 * SysExt.cl 1 * SysExt.cl 2 * SysExt.cl 3 * SysExt.cl 4 * SysExt.cl 5 := by
  simp only [wholeEven, MulMemClass.coe_mul, SysExt.singletLine_val, SysExt.lineLine_val]
  simp only [mul_assoc]
  rfl

/-- **Proposition 37 (one step joins the two).** `𝒯 = J(a)Λ(U)` is gauge-transformed like one transport,
`Λ(g_x)𝒯_{xy}Λ(g_y)⁻¹ = J(g_xa)Λ(g_xU_{xy}g_y⁻¹)`, for every connection of P4 with values in the rotations of the six;
`𝒯_{xy}⁻¹ = J(U_{yx}a)Λ(U_{yx})` for a unit direction; on the four amplitudes the even words of the step are all the
operators (an isomorphism of real algebras from the even Clifford algebra of the six), with `J_nJ_t ↦ −iγ_t`,
`J_sJ_t ↦ γ_sγ_t`, `w ↦ −i`; so a step of one system along `t` is `γ_t = i J_nJ_t`, two vertical steps; the vertical
steps on the sixty-four sets are a faithful representation of the Clifford algebra of the six.

Recognition: the four amplitudes are the spinor of the six; the quantum `i` is the whole `w`. Uses Props. 4, 5, 33,
P4, Definitions 24, 26. -/
theorem prop_37 {n : ℕ} {X : Type*} :
    (∀ (a : Fin n → ℝ) (U gx gy : Matrix (Fin n) (Fin n) ℝ), gxᵀ * gx = 1 →
      SysExt.extMap gx * SysExt.jointStep a U * SysExt.extMap gyᵀ =
        SysExt.jointStep (gx *ᵥ a) (gx * U * gyᵀ)) ∧
    (∀ (c : Connection X (SysExt.Rot n)) (g : X → SysExt.Rot n) (a : Fin n → ℝ) (x y : X),
      SysExt.extMap (g x : Matrix (Fin n) (Fin n) ℝ) * SysExt.connStep c a x y *
          SysExt.extMap ((g y)⁻¹ : SysExt.Rot n) =
        SysExt.connStep (c.rename g) ((g x : Matrix (Fin n) (Fin n) ℝ) *ᵥ a) x y) ∧
    (∀ (c : Connection X (SysExt.Rot n)) (a : Fin n → ℝ), a ⬝ᵥ a = 1 → ∀ x y : X,
      SysExt.connStep c a x y * SysExt.connStep c ((c.U y x : Matrix (Fin n) (Fin n) ℝ) *ᵥ a) y x = 1 ∧
      SysExt.connStep c ((c.U y x : Matrix (Fin n) (Fin n) ℝ) *ᵥ a) y x * SysExt.connStep c a x y = 1) ∧
    Function.Bijective SysExt.evenToFour ∧
    (∀ t : Fin 5, SysExt.evenToFour (SysExt.singletLine t) = (-Complex.I) • γ t) ∧
    (∀ s t : Fin 5, SysExt.evenToFour (SysExt.lineLine s t) = γ s * γ t) ∧
    SysExt.evenToFour wholeEven = (-Complex.I) • (1 : Matrix Four Four ℂ) ∧
    (wholeEven : CliffordAlgebra SysExt.Q6) =
      SysExt.cl 0 * SysExt.cl 1 * SysExt.cl 2 * SysExt.cl 3 * SysExt.cl 4 * SysExt.cl 5 ∧
    (∀ t : Fin 5, γ t = Complex.I • SysExt.evenToFour (SysExt.singletLine t)) ∧
    Function.Injective SysExt.stepRep ∧ (∀ a : Fin 6, SysExt.stepRep (SysExt.cl a) = SysExt.Jx a) := by
  refine ⟨fun a U gx gy hgx => SysExt.jointStep_rename a U gx gy hgx, SysExt.connStep_rename,
    fun c a ha x y => SysExt.connStep_inv c a ha x y, SysExt.evenToFour_bijective, SysExt.evenToFour_singlet_line,
    SysExt.evenToFour_line_line, ?_, wholeEven_val, SysExt.line_eq_i_singlet_line, SysExt.stepRep_injective,
    SysExt.stepRep_cl⟩
  rw [wholeEven, map_mul, map_mul, SysExt.evenToFour_singlet_line, SysExt.evenToFour_line_line,
    SysExt.evenToFour_line_line]
  have hprod : γ 0 * (γ 1 * γ 2) * (γ 3 * γ 4) = 1 := by
    rw [← γ_prod]
    simp only [mul_assoc]
  rw [smul_mul_assoc, smul_mul_assoc, hprod]

/-! ## Proposition 38 -/

theorem curv_rename {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (c : Connection (Fin 16) (Matrix n n R)ˣ) (g : Fin 16 → (Matrix n n R)ˣ) (x : Fin 16) (s t : Fin 5) :
    curv (c.rename g) x s t =
      (g x : Matrix n n R) * curv c x s t * ((g x)⁻¹ : (Matrix n n R)ˣ) := by
  have h := hol_rename_closed c g x [transition t x, transition s (transition t x), transition t (transition s (transition t x)),
    transition s (transition t (transition s (transition t x)))] (by
      simp only [List.getLast_cons_cons, List.getLast_singleton]
      exact Article.square_closed t s x)
  simp only [curv, squarePlaces]
  rw [h, Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]

/-- **Proposition 38 (curvature).** The curvature `F_st(x) = hol(x; tsts) − 1` turns under a gauge transformation by
the gauge at its vertex, `F_st(x) ↦ g_xF_st(x)g_x⁻¹`; every closed walk of four steps is a square `tsts`; ten
squares pass through each vertex and there are forty in all; for `U_{xy} = e^{a_{xy}}` near one, with `a₁, …, a₄`
the rotations of the four steps in order, `hol = exp(Σ aᵢ + ½ Σ_{i>j}[aᵢ, aⱼ] + O(a³))`, that is
`log hol = Σ aᵢ + ½ Σ_{i>j}[aᵢ, aⱼ] + O(a³)` (along `a ↦ ta`, with the remainder `O(t³)`).

Recognition: the curvature is the force, `F = dA + A ∧ A` when the vertices are many and the rotations small; the sixteen
vertices and the forty squares build `ℝP⁴`. Uses Props. 25, 32, Definition 25. -/
theorem prop_38 :
    (∀ {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (c : Connection (Fin 16) (Matrix n n R)ˣ)
      (g : Fin 16 → (Matrix n n R)ˣ) (x : Fin 16) (s t : Fin 5),
      curv (c.rename g) x s t = (g x : Matrix n n R) * curv c x s t * ((g x)⁻¹ : (Matrix n n R)ˣ)) ∧
    (∀ (x : Fin 16) (a b c d : Fin 5), a ≠ b → b ≠ c → c ≠ d → d ≠ a →
      transition d (transition c (transition b (transition a x))) = x → a = c ∧ b = d) ∧
    (∀ x : Fin 16, (Finset.image (fun p : Fin 5 × Fin 5 => square x p.1 p.2)
      (Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 < p.2)).card = 10) ∧
    (Finset.image (fun p : Fin 16 × Fin 5 × Fin 5 => square p.1 p.2.1 p.2.2)
      (Finset.univ.filter fun p : Fin 16 × Fin 5 × Fin 5 => p.2.1 < p.2.2)).card = 40 ∧
    (∀ {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (a₁ a₂ a₃ a₄ : A),
      (fun t : ℝ => NormedSpace.exp (t • a₄) * NormedSpace.exp (t • a₃) * NormedSpace.exp (t • a₂) *
          NormedSpace.exp (t • a₁) -
        NormedSpace.exp (t • (a₁ + a₂ + a₃ + a₄) + (t ^ 2) • ((1 / 2 : ℝ) • Article.squareC a₁ a₂ a₃ a₄)))
        =O[nhds 0] fun t : ℝ => t ^ 3) := by
  refine ⟨fun c g x s t => curv_rename c g x s t, four_cycles, ?_, card_squares,
    fun a₁ a₂ a₃ a₄ => Article.bch_line a₁ a₂ a₃ a₄⟩
  decide +kernel

/-! ## Proposition 39 -/

/-- **Proposition 39 (kept and moved: the mass form).** `M_D(X, X) = ‖[X, P_D]‖² ≥ 0`, zero exactly when `X` is kept;
`M_D = 2` on every unit moved rotation `E_ab − E_ba` (`a ∈ D`, `b ∉ D`); between neighbouring vertices
`DP_D = U_{xy}P_D(y)U_{xy}⁻¹ − P_D(x) ↦ g_x(DP_D)g_x⁻¹`; near one, with `U = 1 + A`,
`DP_D = (P_D(y) − P_D(x)) + [A, P_D] + O(A²)`; with `q_D = 1 + (i − 1)P_D`, `Dq_D = (i − 1)DP_D` and
`‖Dq_D‖² = 2‖DP_D‖²`; along a rotation `X`, `‖Dq_D‖² = 2M_D(X, X)`.

Recognition: the kept rotations are massless gauge fields and the moved rotations massive (Englert, Brout, Higgs). Uses
Prop. 21, Definitions 15, 27. -/
theorem prop_39 {n : ℕ} :
    (∀ (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ),
      massForm D X X = ∑ i, ∑ j, ((X * projD D - projD D * X) i j) ^ 2 ∧ 0 ≤ massForm D X X ∧
      (massForm D X X = 0 ↔ X * thetaD D = thetaD D * X)) ∧
    (∀ (D : Finset (Fin n)) (a b : Fin n), a ∈ D → b ∉ D → massForm D (unitTurn a b) (unitTurn a b) = 2) ∧
    (∀ U Px Py gx gy : Matrix (Fin n) (Fin n) ℝ, gyᵀ * gy = 1 →
      covDiff (gx * U * gyᵀ) (gx * Px * gxᵀ) (gy * Py * gyᵀ) = gx * covDiff U Px Py * gxᵀ) ∧
    (∀ A Px Py : Matrix (Fin n) (Fin n) ℝ, Aᵀ = -A →
      covDiff (1 + A) Px Py = (Py - Px) + (A * Py - Py * A) - A * Py * A) ∧
    (∀ U Px Py : Matrix (Fin n) (Fin n) ℝ, U * Uᵀ = 1 →
      covDiffC U (qHalf Px) (qHalf Py) = (Complex.I - 1) • toC (covDiff U Px Py)) ∧
    (∀ M : Matrix (Fin n) (Fin n) ℝ, frobSq ((Complex.I - 1) • toC M) = 2 * ∑ i, ∑ j, M i j ^ 2) ∧
    (∀ (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ),
      frobSq ((Complex.I - 1) • toC (X * projD D - projD D * X)) = 2 * massForm D X X) :=
  ⟨fun D X => ⟨massForm_self_eq D X, massForm_nonneg D X, massForm_eq_zero_iff D X⟩,
    fun D a b ha hb => massForm_unit_moved D ha hb, covDiff_rename, covDiff_near_one, covDiff_half, frobSq_half,
    half_mass⟩

/-! ## Proposition 91 -/

/-- The Clebsch graph on the sixteen vertices: two vertices are linked when one step leads from one to the other. -/
def clebsch : SimpleGraph (Fin 16) where
  Adj x y := Adjacent x y
  symm := ⟨fun x y h => (adjacent_symm x y).mp h⟩
  loopless := ⟨fun x h => by
    obtain ⟨t, ht⟩ := h
    exact transition_ne t x ht⟩

instance : DecidableRel clebsch.Adj := fun x y => inferInstanceAs (Decidable (Adjacent x y))

theorem clebsch_reachable_word (w : List (Fin 5)) : clebsch.Reachable 0 (relOfWord w) := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl 0
  | cons t w ih =>
    have hadj : clebsch.Adj (relOfWord w) (relOfWord (t :: w)) := ⟨t, rfl⟩
    exact ih.trans hadj.reachable

/-- **The vertices are connected.** -/
theorem clebsch_preconnected : clebsch.Preconnected := by
  intro u v
  obtain ⟨w₁, -, rfl⟩ := relOfWord_surjective u
  obtain ⟨w₂, -, rfl⟩ := relOfWord_surjective v
  exact (clebsch_reachable_word w₁).symm.trans (clebsch_reachable_word w₂)

/-- The kept rotations of a division of P1's real six, a real vector space. -/
def keptSub (D : Finset (Fin 6)) : Submodule ℝ (Matrix (Fin 6) (Fin 6) ℝ) where
  carrier := {X | Formulas.KeptAt D X}
  add_mem' := by
    rintro X Y ⟨hX1, hX2⟩ ⟨hY1, hY2⟩
    refine ⟨by rw [Matrix.transpose_add, hX1, hY1, neg_add], ?_⟩
    rw [Matrix.add_mul, Matrix.mul_add, hX2, hY2]
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro c X ⟨hX1, hX2⟩
    refine ⟨by rw [Matrix.transpose_smul, hX1, smul_neg], ?_⟩
    rw [Matrix.smul_mul, Matrix.mul_smul, hX2]

/-- **The centre of the kept rotations** of a division: the kept rotations that commute with every kept rotation. -/
def centreSub (D : Finset (Fin 6)) : Submodule ℝ (Matrix (Fin 6) (Fin 6) ℝ) where
  carrier := {X | Formulas.CentralAt D X}
  add_mem' := by
    rintro X Y ⟨hX1, hX2⟩ ⟨hY1, hY2⟩
    refine ⟨(keptSub D).add_mem hX1 hY1, fun Z hZ => ?_⟩
    rw [Matrix.add_mul, Matrix.mul_add, hX2 Z hZ, hY2 Z hZ]
  zero_mem' := ⟨(keptSub D).zero_mem, fun Z _ => by simp⟩
  smul_mem' := by
    rintro c X ⟨hX1, hX2⟩
    refine ⟨(keptSub D).smul_mem c hX1, fun Z hZ => ?_⟩
    rw [Matrix.smul_mul, Matrix.mul_smul, hX2 Z hZ]

theorem mem_centreSub (D : Finset (Fin 6)) (X : Matrix (Fin 6) (Fin 6) ℝ) :
    X ∈ centreSub D ↔ Formulas.CentralAt D X := Iff.rfl

theorem pair_part_finite : ∀ a b i j : Fin 6, a ≠ b → i ≠ j →
    ((i ∈ ({a, b} : Finset (Fin 6)) ↔ j ∈ ({a, b} : Finset (Fin 6))) ∧
      ∀ c, (c ∈ ({a, b} : Finset (Fin 6)) ↔ i ∈ ({a, b} : Finset (Fin 6))) → c = i ∨ c = j) →
    (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  decide +kernel

/-- **At a part of two directions the centre is the rotation of that plane:** every central kept rotation is
`X_ab (E_ab − E_ba)`. -/
theorem central_eq_smul {a b : Fin 6} (hab : a ≠ b) {X : Matrix (Fin 6) (Fin 6) ℝ}
    (hX : Formulas.CentralAt {a, b} X) : X = X a b • unitTurn a b := by
  have hskew : ∀ i j, X j i = -X i j := fun i j => by
    have := congrFun (congrFun hX.1.1 i) j
    simpa using this
  have hcent : ∀ b' c' : Fin 6, (b' ∈ ({a, b} : Finset (Fin 6)) ↔ c' ∈ ({a, b} : Finset (Fin 6))) →
      X * unitTurn b' c' = unitTurn b' c' * X := fun b' c' h =>
    hX.2 _ ⟨unitTurn_transpose b' c', Formulas.unitTurn_comm_thetaD _ b' c' h⟩
  have key : ∀ i j, X i j ≠ 0 → (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      have := hskew i i
      exact hij (by linarith)
    exact pair_part_finite a b i j hab hne (clock_dividedSet _ X hX.1.2 hcent hne hij)
  ext i j
  simp only [Matrix.smul_apply, unitTurn, Matrix.of_apply, smul_eq_mul]
  by_cases hij : (i = a ∧ j = b)
  · obtain ⟨rfl, rfl⟩ := hij
    simp [hab]
  · by_cases hji : (i = b ∧ j = a)
    · obtain ⟨rfl, rfl⟩ := hji
      have := hskew i j
      simp [hab, Ne.symm hab]
      linarith
    · have h0 : X i j = 0 := by
        by_contra h
        rcases key i j h with h' | h'
        · exact hij h'
        · exact hji h'
      simp [h0, hij, hji]

theorem unitTurn_ne_zero {a b : Fin 6} (hab : a ≠ b) : unitTurn a b ≠ 0 := by
  intro h
  have := congrFun (congrFun h a) b
  simp [unitTurn, hab] at this

theorem centreSub_pair {a b : Fin 6} (hab : a ≠ b) :
    centreSub {a, b} = Submodule.span ℝ {unitTurn a b} := by
  apply le_antisymm
  · intro X hX
    rw [central_eq_smul hab hX]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Formulas.unitTurn_central_pair hab

theorem centreSub_compl (D : Finset (Fin 6)) : centreSub Dᶜ = centreSub D := by
  ext X
  exact Formulas.centralAt_compl D X

/-- **The dimension of the centre of the kept rotations:** one at a part of two directions, zero otherwise. -/
theorem finrank_centreSub (D : Finset (Fin 6)) :
    Module.finrank ℝ (centreSub D) = if D.card = 2 ∨ D.card = 4 then 1 else 0 := by
  by_cases h : D.card = 2 ∨ D.card = 4
  · rw [if_pos h]
    rcases h with h2 | h4
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
      rw [centreSub_pair hab, finrank_span_singleton (unitTurn_ne_zero hab)]
    · have hc : Dᶜ.card = 2 := by rw [Finset.card_compl, Fintype.card_fin, h4]
      obtain ⟨a, b, hab, hD⟩ := Finset.card_eq_two.mp hc
      rw [← centreSub_compl, hD, centreSub_pair hab, finrank_span_singleton (unitTurn_ne_zero hab)]
  · rw [if_neg h]
    have hbot : centreSub D = ⊥ := by
      rw [eq_bot_iff]
      intro X hX
      by_contra hne
      exact h (Formulas.card_of_central hX hne)
    rw [hbot, finrank_bot]

theorem rotMat_eq (p : Fin 6 × Fin 6) (hp : p.1 ≠ p.2) :
    (rotMat p).map (Int.cast : ℤ → ℝ) = (-2 : ℝ) • unitTurn p.1 p.2 := by
  ext d c
  simp only [Matrix.map_apply, rotMat, Matrix.of_apply, Matrix.smul_apply, unitTurn, smul_eq_mul]
  by_cases h1 : d = p.2 ∧ c = p.1
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hp, Ne.symm hp]
  · by_cases h2 : d = p.1 ∧ c = p.2
    · obtain ⟨rfl, rfl⟩ := h2
      simp [hp, Ne.symm hp]
    · simp [h1, h2]

/-- **Proposition 91 (the common clock).** Phases `q_{xy} = q_{yx}⁻¹` in `U(1)` on the forty links of the sixteen
vertices have a common phase, `z_x = q_{xy}z_y` on every link, exactly when the product of `q` around every closed walk
is one (the vertices being connected); the flat sign `q ≡ −1` closes every square with `(−1)⁴ = +1` and the closed
walk `12345` with `(−1)⁵ = −1`, so it has no common phase; the centre of the kept rotations has dimension `0, 0, 1, 0`
at the types `0|6, 1|5, 2|4, 3|3` (and their complements), at `2|4` the rotation of the two-direction part, which at the
plane `F = \{h, k\}` is the action of the plane's rotation `γ_hγ_k` on the six.

Recognition: the common time of electromagnetism; the field is the obstruction to it, which the Aharonov–Bohm phase
measures; the flat sign is the loop of `ℝP⁴`. Uses Props. 25, 38, 41, Definition 28. -/
theorem prop_91 :
    (∀ q : Fin 16 → Fin 16 → Circle, (∀ x y, q y x = (q x y)⁻¹) →
      ((∃ z : Fin 16 → Circle, ∀ x y, clebsch.Adj x y → z x = q x y * z y) ↔
        ∀ (u : Fin 16) (p : clebsch.Walk u u), ArticleStatements.Clock.walkProd (fun x y => q y x) p = 1)) ∧
    clebsch.Preconnected ∧
    (Finset.univ.filter fun p : Fin 16 × Fin 16 => p.1 < p.2 ∧ Adjacent p.1 p.2).card = 40 ∧
    (∀ (a b : Fin 5) (r : Fin 16), transition b (transition a (transition b (transition a r))) = r) ∧ ((-1 : ℂ) ^ 4 = 1) ∧
    (∀ r : Fin 16, transition 4 (transition 3 (transition 2 (transition 1 (transition 0 r)))) = r) ∧ ((-1 : ℂ) ^ 5 = -1) ∧
    (¬ ∃ z : Fin 16 → Circle, ∀ (t : Fin 5) (x : Fin 16), (z (transition t x) : ℂ) = -(z x : ℂ)) ∧
    (∀ D : Finset (Fin 6), Module.finrank ℝ (centreSub D) = if D.card = 2 ∨ D.card = 4 then 1 else 0) ∧
    (∀ a b : Fin 6, a ≠ b → centreSub {a, b} = Submodule.span ℝ {unitTurn a b}) ∧
    (∀ f : Fin 10, plane (Sum.inr f) = ((Comparison.planeLines f).1.succ, (Comparison.planeLines f).2.succ) ∧
      (rotMat (plane (Sum.inr f))).map (Int.cast : ℤ → ℝ) =
        (-2 : ℝ) • unitTurn (Comparison.planeLines f).1.succ (Comparison.planeLines f).2.succ ∧
      gen (Sum.inr f) = -(γ (Comparison.planeLines f).1 * γ (Comparison.planeLines f).2) ∧
      ∀ c : Fin 6, act (gen (Sum.inr f)) (sixP1 c) =
        ∑ d, ((rotMat (plane (Sum.inr f)) d c : ℤ) : ℂ) • sixP1 d) := by
  refine ⟨fun q hq => ?_, clebsch_preconnected, card_edges, fun a b r => Article.square_closed a b r,
    by norm_num, Article.history_12345_closed, by norm_num, ?_, finrank_centreSub,
    fun a b hab => centreSub_pair hab, fun f => ?_⟩
  · have hg : ∀ x y, (fun x y => q y x) y x = ((fun x y => q y x) x y)⁻¹ := fun x y => by
      change q x y = (q y x)⁻¹
      rw [hq x y, inv_inv]
    rw [← ArticleStatements.Clock.clock_iff_loops (fun x y => q y x) hg clebsch_preconnected 0]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, fun x y hxy => ?_⟩
      change q y x = z y / z x
      have h := hz y x (clebsch.adj_symm hxy)
      rw [h]
      simp
    · rintro ⟨φ, hφ⟩
      refine ⟨φ, fun x y hxy => ?_⟩
      have h : q x y = φ x / φ y := hφ y x (clebsch.adj_symm hxy)
      rw [h]
      simp
  · rintro ⟨z, hz⟩
    have h0 := Article.flat_sign_no_clock (fun x => (z x : ℂ)) hz
    have := congrFun h0 0
    simp only [Pi.zero_apply] at this
    exact (Circle.coe_ne_zero (z 0)) this
  · have hpl : plane (Sum.inr f) = ((Comparison.planeLines f).1.succ, (Comparison.planeLines f).2.succ) := rfl
    refine ⟨hpl, ?_, gen_inr f, fun c => gen_acts_matrix (Sum.inr f) c⟩
    rw [rotMat_eq _ (ne_of_lt (plane_lt (Sum.inr f))), hpl]

end Comparison.System.Existence
