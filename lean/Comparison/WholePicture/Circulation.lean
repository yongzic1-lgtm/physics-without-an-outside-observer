module

public import Comparison.Existence.PlaquetteData

/-!
# The whole picture, statement 17: the long-range zero under a circulation on the links

Phases `θ` on the forty links (`linkU ℓ < linkV ℓ`,
`PlaquetteData`) make the step of the sixteen vertices `A_θ` (`magAdj`): `e^{iθ_ℓ}` from
`U_ℓ` to `V_ℓ` and `e^{−iθ_ℓ}` back. Its quadratic form is
`magForm θ v = Σ_ℓ 2 Re(e^{iθ_ℓ} v̄_{V_ℓ} v_{U_ℓ})` (`magForm_eq`), and `lamMax θ` the supremum of
`magForm θ v/‖v‖²`.

* **The vertices.** `incZ` (the incidence), `adjZ` (the adjacency, the square of the signed step,
  `adjZ_links`); `incZ_gram`: `NNᵀ = 5 − A`; `green_identity_local`: `(5 − A)·128G = 128 − 8J` with
  `128G = 4(7 + A) − 3J` (`green_identity`, restated here because `CriticalGerm.lean` is
  a file outside the module system); `adj_srg`: **`A² = 3 − 2A + 2J`**, the Clebsch graph.
* **The cyclic part.** `divR`, `gradR`, `thetaCyc θ = θ − grad G div θ`: `divR_thetaCyc` (no
  divergence), `theta_sub_cyc` (`θ − θ_cyc` is a gradient), `cyc_unique` (**the part no gauge transformation
  removes is unique**), `sqL_cyc_le` (`‖θ_cyc‖² ≤ ‖θ‖²`).
* **The largest value is the largest eigenvalue.** `magAdj_isHermitian`; `lamMax_hasEigenvalue`:
  `lamMax θ` is an eigenvalue of `A_θ`; `eigen_le_lamMax`: every eigenvalue is at most `lamMax θ`.
  So `lamMax θ = λ_max(A_θ)`. `lamMax_gauge`: **a gauge transformation does not move it**,
  `λ_max(A_{θ + grad φ}) = λ_max(A_θ)`; `lamMax_cyc`: it depends on `θ_cyc` only.
* **The two bounds.** `lamMax_ge`: `λ_max(A_θ) ≥ 5 − ‖θ‖²/16` (the constant vector); `clebsch_le`:
  on functions of mean zero `y†Ay ≤ ‖y‖²` (`(1 − A)² = 4(1 − A) + 2J`); `cross_term_le`: the cross
  term of a field without divergence is of second order; `lamMax_upper`:
  **`λ_max(A_ψ) ≤ 5 − ‖ψ‖²/16 + ‖ψ‖⁴/10`** for `div ψ = 0`, `‖ψ‖² ≤ 1/100`.
* **The long-range zero.** `ucrit θ = (λ − √(λ² − 16))/8`, `ucrit_root`: `1 + 4u_c² = u_c λ_max`;
  `log_root_bound`; `long_range_zero`: with `‖θ_cyc‖² ≤ 1/100`,
  **`|λ_max(A_θ) − (5 − ‖θ_cyc‖²/16)| ≤ ‖θ_cyc‖⁴/10`** and
  **`|log 4u_c − ‖θ_cyc‖²/48| ≤ ‖θ_cyc‖⁴/20`**: `λ_max = 5 − ‖θ_cyc‖²/16 + O(θ⁴)` and
  `log 4u_c = ‖θ_cyc‖²/48 + O(θ⁴)`.
-/

@[expose] public section

namespace Comparison.WholePicture

open Complex Matrix

/-! ## The vertices, the links and the cyclic part of the phases -/

/-- The incidence of vertices and links: `N_{xℓ} = [V_ℓ = x] − [U_ℓ = x]`. -/
def incZ (x : Fin 16) (l : Fin 40) : ℤ :=
  (if linkV l = x then 1 else 0) - (if linkU l = x then 1 else 0)

/-- The adjacency of the sixteen vertices: `1` on the forty links (the square of the signed step). -/
def adjZ (x y : Fin 16) : ℤ := sadjZ x y * sadjZ x y

/-- The two ends of the link `l` as an indicator: `1` when `(x, y)` is `(V, U)` or `(U, V)`. -/
def linkInd (l : Fin 40) (x y : Fin 16) : ℤ :=
  (if x = linkV l then (if y = linkU l then 1 else 0) else 0) +
    (if x = linkU l then (if y = linkV l then 1 else 0) else 0)

/-- The adjacency is carried by the forty links. -/
theorem adjZ_links : ∀ x y : Fin 16, adjZ x y = ∑ l, linkInd l x y := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- `N Nᵀ = 5 − A`: the divergence of a gradient is the Laplacian of the vertices. -/
theorem incZ_gram : ∀ x y : Fin 16,
    ∑ l, incZ x l * incZ y l = (if x = y then 5 else 0) - adjZ x y := by
  decide +kernel

/-- Every link has one head and one tail. -/
theorem incZ_col : ∀ l : Fin 40, ∑ x, incZ x l = 0 := by decide

/-- Every vertex is an end of five links. -/
theorem ends_count : ∀ x : Fin 16,
    ∑ l, ((if linkV l = x then 1 else 0) + (if linkU l = x then 1 else 0) : ℤ) = 5 := by
  decide +kernel

/-- `128 G = 4(7 + A) − 3J`, the Green function of the vertices (`green_identity`). -/
def green128 (x y : Fin 16) : ℤ := 4 * ((if x = y then 7 else 0) + adjZ x y) - 3

set_option maxRecDepth 10000 in
/-- `(5 − A)·128G = 128 − 8J`. -/
theorem green_identity_local : ∀ x y : Fin 16,
    ∑ z, ((if x = z then 5 else 0) - adjZ x z) * green128 z y = (if x = y then 128 else 0) - 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- **The vertices are the Clebsch graph:** `A² = 3 − 2A + 2J`. -/
theorem adj_srg : ∀ x y : Fin 16,
    ∑ z, adjZ x z * adjZ z y = (if x = y then 3 else 0) - 2 * adjZ x y + 2 := by
  decide +kernel

theorem adj_symm : ∀ x y : Fin 16, adjZ x y = adjZ y x := by decide

/-- The divergence of phases on the links. -/
def divR (θ : Fin 40 → ℝ) (x : Fin 16) : ℝ := ∑ l, (incZ x l : ℝ) * θ l

/-- The gradient of a function on the vertices: `(grad φ)_ℓ = φ(V_ℓ) − φ(U_ℓ)`. -/
def gradR (φ : Fin 16 → ℝ) (l : Fin 40) : ℝ := ∑ x, (incZ x l : ℝ) * φ x

/-- The Green function applied to a function on the vertices. -/
noncomputable def greenR (f : Fin 16 → ℝ) (x : Fin 16) : ℝ := (∑ y, (green128 x y : ℝ) * f y) / 128

/-- **The cyclic part** of the phases: `θ_cyc = θ − grad G div θ`. -/
noncomputable def thetaCyc (θ : Fin 40 → ℝ) : Fin 40 → ℝ := fun l => θ l - gradR (greenR (divR θ)) l

theorem gradR_apply (φ : Fin 16 → ℝ) (l : Fin 40) : gradR φ l = φ (linkV l) - φ (linkU l) := by
  simp only [gradR, incZ]
  push_cast
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem div_grad (φ : Fin 16 → ℝ) (x : Fin 16) :
    divR (gradR φ) x = ∑ y, (((if x = y then 5 else 0) - adjZ x y : ℤ) : ℝ) * φ y := by
  simp only [divR, gradR, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← incZ_gram x y]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem sum_divR (θ : Fin 40 → ℝ) : ∑ x, divR θ x = 0 := by
  simp only [divR]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [← Finset.sum_mul]
  have h := congrArg (fun z : ℤ => (z : ℝ)) (incZ_col l)
  push_cast at h
  rw [h, zero_mul]

/-- **The Green function inverts the Laplacian on functions of mean zero.** -/
theorem laplace_green (f : Fin 16 → ℝ) (x : Fin 16) :
    ∑ y, (((if x = y then 5 else 0) - adjZ x y : ℤ) : ℝ) * greenR f y = f x - (∑ y, f y) / 16 := by
  have hz : ∀ z, ∑ y, (((if x = y then 5 else 0) - adjZ x y : ℤ) : ℝ) * (green128 y z : ℝ) =
      (((if x = z then 128 else 0) - 8 : ℤ) : ℝ) := by
    intro z
    rw [← green_identity_local x z]
    push_cast
    rfl
  calc ∑ y, (((if x = y then 5 else 0) - adjZ x y : ℤ) : ℝ) * greenR f y
      = (∑ z, (∑ y, (((if x = y then 5 else 0) - adjZ x y : ℤ) : ℝ) * (green128 y z : ℝ)) * f z) /
          128 := by
        simp only [greenR, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
        ring
    _ = (∑ z, (((if x = z then 128 else 0) - 8 : ℤ) : ℝ) * f z) / 128 := by
        simp only [hz]
    _ = f x - (∑ y, f y) / 16 := by
        push_cast
        simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true, ← Finset.mul_sum]
        ring

/-- **The cyclic part has no divergence.** -/
theorem divR_thetaCyc (θ : Fin 40 → ℝ) (x : Fin 16) : divR (thetaCyc θ) x = 0 := by
  have hlin : divR (thetaCyc θ) x = divR θ x - divR (gradR (greenR (divR θ))) x := by
    simp only [divR, thetaCyc, mul_sub, Finset.sum_sub_distrib]
  rw [hlin, div_grad, laplace_green, sum_divR]
  ring

/-- `θ − θ_cyc` is a gradient. -/
theorem theta_sub_cyc (θ : Fin 40 → ℝ) : θ = thetaCyc θ + gradR (greenR (divR θ)) := by
  ext l
  simp [thetaCyc]

/-- A gradient is orthogonal to a field without divergence. -/
theorem grad_orth (φ : Fin 16 → ℝ) (ψ : Fin 40 → ℝ) (hψ : ∀ x, divR ψ x = 0) :
    ∑ l, gradR φ l * ψ l = 0 := by
  simp only [gradR, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x _ => ?_
  have h := hψ x
  simp only [divR] at h
  calc ∑ l, (incZ x l : ℝ) * φ x * ψ l = φ x * ∑ l, (incZ x l : ℝ) * ψ l := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = 0 := by rw [h, mul_zero]

/-- The squared length of phases. -/
def sqL (θ : Fin 40 → ℝ) : ℝ := ∑ l, θ l ^ 2

/-- **The cyclic part is the shortest:** `‖θ_cyc‖² ≤ ‖θ‖²`. -/
theorem sqL_cyc_le (θ : Fin 40 → ℝ) : sqL (thetaCyc θ) ≤ sqL θ := by
  have horth := grad_orth (greenR (divR θ)) (thetaCyc θ) (divR_thetaCyc θ)
  have e := theta_sub_cyc θ
  have h : sqL θ = sqL (thetaCyc θ) + sqL (gradR (greenR (divR θ))) := by
    simp only [sqL]
    conv_lhs => rw [e]
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib]
    have : ∑ l, 2 * thetaCyc θ l * gradR (greenR (divR θ)) l =
        2 * ∑ l, gradR (greenR (divR θ)) l * thetaCyc θ l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [this, horth]
    ring
  have : 0 ≤ sqL (gradR (greenR (divR θ))) := Finset.sum_nonneg fun l _ => sq_nonneg _
  linarith

/-- **The cyclic part is the part no gauge transformation removes:** any splitting `θ = grad φ + ψ` with `ψ`
divergence-free has `ψ = θ_cyc`. -/
theorem cyc_unique (θ : Fin 40 → ℝ) (φ : Fin 16 → ℝ) (ψ : Fin 40 → ℝ) (hψ : ∀ x, divR ψ x = 0)
    (h : θ = gradR φ + ψ) : ψ = thetaCyc θ := by
  set d : Fin 40 → ℝ := fun l => ψ l - thetaCyc θ l
  have hd : d = gradR (greenR (divR θ) - φ) := by
    ext l
    have e1 := congrFun h l
    have e2 := congrFun (theta_sub_cyc θ) l
    simp only [Pi.add_apply] at e1 e2
    simp only [d, gradR_apply, Pi.sub_apply]
    rw [gradR_apply] at e1 e2
    linarith
  have hdiv : ∀ x, divR d x = 0 := by
    intro x
    have : divR d x = divR ψ x - divR (thetaCyc θ) x := by
      simp only [divR, d, mul_sub, Finset.sum_sub_distrib]
    rw [this, hψ x, divR_thetaCyc]
    ring
  have h0 : ∑ l, d l * d l = 0 := by
    conv_lhs => arg 2; ext l; rw [show d l * d l = (gradR (greenR (divR θ) - φ)) l * d l by rw [hd]]
    exact grad_orth _ d hdiv
  ext l
  have hl : d l = 0 := by
    have hnn : ∀ m ∈ Finset.univ, 0 ≤ d m * d m := fun m _ => mul_self_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 l (Finset.mem_univ l)
    exact mul_self_eq_zero.mp this
  simp only [d] at hl
  linarith


/-! ## The magnetic step and its largest value -/

/-- **The quadratic form of the step with phases on the links:**
`Re v†A_θ v = Σ_ℓ 2 Re(e^{iθ_ℓ} v̄_{V_ℓ} v_{U_ℓ})`, `A_θ` carrying `e^{iθ_ℓ}` from `U_ℓ` to `V_ℓ`
and `e^{−iθ_ℓ}` back. -/
noncomputable def magForm (θ : Fin 40 → ℝ) (v : Fin 16 → ℂ) : ℝ :=
  ∑ l, 2 * (exp (θ l * I) * star (v (linkV l)) * v (linkU l)).re

/-- `‖v‖²`. -/
noncomputable def nsq (v : Fin 16 → ℂ) : ℝ := ∑ x, Complex.normSq (v x)

theorem nsq_nonneg (v : Fin 16 → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem nsq_pos {v : Fin 16 → ℂ} (hv : v ≠ 0) : 0 < nsq v := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hv
  have hx' : 0 < Complex.normSq (v x) := Complex.normSq_pos.mpr hx
  exact lt_of_lt_of_le hx' (Finset.single_le_sum (fun y _ => Complex.normSq_nonneg (v y))
    (Finset.mem_univ x))

/-- The sum over the links of a function of the head and of the tail is five times the sum over
the vertices. -/
theorem sum_ends (f : Fin 16 → ℝ) : ∑ l, (f (linkV l) + f (linkU l)) = 5 * ∑ x, f x := by
  have h : ∀ l, f (linkV l) + f (linkU l) =
      ∑ x, f x * (((if linkV l = x then 1 else 0) + (if linkU l = x then 1 else 0) : ℤ) : ℝ) := by
    intro l
    push_cast
    simp only [mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  rw [Finset.sum_congr rfl fun l _ => h l, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, ← Int.cast_sum, ends_count x]
  push_cast
  ring

theorem re_term_le (e a b : ℂ) (he : ‖e‖ = 1) :
    2 * (e * star a * b).re ≤ Complex.normSq a + Complex.normSq b := by
  have h1 : (e * star a * b).re ≤ ‖e * star a * b‖ := Complex.re_le_norm _
  rw [norm_mul, norm_mul, he, one_mul, norm_star] at h1
  have h2 : 2 * (‖a‖ * ‖b‖) ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  linarith

/-- **The form is at most five times the length:** `magForm θ v ≤ 5‖v‖²`. -/
theorem magForm_le (θ : Fin 40 → ℝ) (v : Fin 16 → ℂ) : magForm θ v ≤ 5 * nsq v := by
  calc magForm θ v ≤ ∑ l, (Complex.normSq (v (linkV l)) + Complex.normSq (v (linkU l))) :=
        Finset.sum_le_sum fun l _ => re_term_le _ _ _ (Complex.norm_exp_ofReal_mul_I _)
    _ = 5 * nsq v := by rw [nsq]; exact sum_ends fun x => Complex.normSq (v x)

instance : Nonempty {v : Fin 16 → ℂ // v ≠ 0} :=
  ⟨⟨fun _ => 1, fun h => by simpa using congrFun h 0⟩⟩

/-- **The largest value of the step with phases `θ`:** `λ_max(A_θ) = sup_{v ≠ 0} v†A_θv/‖v‖²`. -/
noncomputable def lamMax (θ : Fin 40 → ℝ) : ℝ :=
  ⨆ v : {v : Fin 16 → ℂ // v ≠ 0}, magForm θ v / nsq v

theorem rayleigh_le_five (θ : Fin 40 → ℝ) (v : {v : Fin 16 → ℂ // v ≠ 0}) :
    magForm θ v / nsq v ≤ 5 := by
  rw [div_le_iff₀ (nsq_pos v.2)]
  exact magForm_le θ v

theorem rayleigh_bdd (θ : Fin 40 → ℝ) :
    BddAbove (Set.range fun v : {v : Fin 16 → ℂ // v ≠ 0} => magForm θ v / nsq v) :=
  ⟨5, by rintro _ ⟨v, rfl⟩; exact rayleigh_le_five θ v⟩

theorem le_lamMax (θ : Fin 40 → ℝ) {v : Fin 16 → ℂ} (hv : v ≠ 0) :
    magForm θ v ≤ lamMax θ * nsq v := by
  have h := le_ciSup (rayleigh_bdd θ) ⟨v, hv⟩
  rw [div_le_iff₀ (nsq_pos hv)] at h
  exact h

theorem lamMax_le (θ : Fin 40 → ℝ) (M : ℝ) (h : ∀ v : Fin 16 → ℂ, v ≠ 0 → magForm θ v ≤ M * nsq v) :
    lamMax θ ≤ M :=
  ciSup_le fun v => by rw [div_le_iff₀ (nsq_pos v.2)]; exact h v v.2

theorem lamMax_le_five (θ : Fin 40 → ℝ) : lamMax θ ≤ 5 :=
  lamMax_le θ 5 fun v _ => magForm_le θ v

/-! ## Renaming: the gauge -/

/-- A gauge transformation of the vertices by phases `φ`. -/
noncomputable def gaugeV (φ : Fin 16 → ℝ) (v : Fin 16 → ℂ) : Fin 16 → ℂ :=
  fun x => exp (φ x * I) * v x

theorem nsq_gauge (φ : Fin 16 → ℝ) (v : Fin 16 → ℂ) : nsq (gaugeV φ v) = nsq v := by
  simp only [nsq, gaugeV, Complex.normSq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.normSq_eq_norm_sq (exp _), Complex.norm_exp_ofReal_mul_I]
  ring

theorem gauge_gauge (φ : Fin 16 → ℝ) (v : Fin 16 → ℂ) : gaugeV φ (gaugeV (-φ) v) = v := by
  ext x
  simp only [gaugeV, Pi.neg_apply, ← mul_assoc, ← Complex.exp_add]
  push_cast
  simp

theorem star_exp_real (r : ℝ) : star (exp (r * I)) = exp (-(r * I)) := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

/-- **A gauge transformation moves the phases by a gradient and keeps the form.** -/
theorem magForm_gauge (θ : Fin 40 → ℝ) (φ : Fin 16 → ℝ) (v : Fin 16 → ℂ) :
    magForm (θ + gradR φ) (gaugeV φ v) = magForm θ v := by
  simp only [magForm, gaugeV]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.add_apply, gradR_apply, star_mul', star_exp_real]
  have h : exp (((θ l + (φ (linkV l) - φ (linkU l)) : ℝ) : ℂ) * I) *
      (exp (-((φ (linkV l) : ℂ) * I)) * star (v (linkV l))) *
        (exp ((φ (linkU l) : ℂ) * I) * v (linkU l)) =
      exp ((θ l : ℂ) * I) * star (v (linkV l)) * v (linkU l) := by
    have e : exp (((θ l + (φ (linkV l) - φ (linkU l)) : ℝ) : ℂ) * I) *
        exp (-((φ (linkV l) : ℂ) * I)) * exp ((φ (linkU l) : ℂ) * I) = exp ((θ l : ℂ) * I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc _ = (exp (((θ l + (φ (linkV l) - φ (linkU l)) : ℝ) : ℂ) * I) *
          exp (-((φ (linkV l) : ℂ) * I)) * exp ((φ (linkU l) : ℂ) * I)) * star (v (linkV l)) *
            v (linkU l) := by ring
      _ = _ := by rw [e]
  rw [h]

/-- **Renaming does not move the largest value:** `λ_max(A_{θ + grad φ}) = λ_max(A_θ)`. -/
theorem lamMax_gauge (θ : Fin 40 → ℝ) (φ : Fin 16 → ℝ) : lamMax (θ + gradR φ) = lamMax θ := by
  apply le_antisymm
  · apply lamMax_le
    intro v hv
    have hw : gaugeV (-φ) v ≠ 0 := by
      intro h0
      apply hv
      rw [← gauge_gauge φ v, h0]
      ext x
      simp [gaugeV]
    have := le_lamMax θ hw
    rw [← magForm_gauge θ φ (gaugeV (-φ) v), gauge_gauge, nsq_gauge] at this
    exact this
  · apply lamMax_le
    intro v hv
    have hw : gaugeV φ v ≠ 0 := by
      intro h0
      apply hv
      have := congrArg (gaugeV (-φ)) h0
      rw [show gaugeV (-φ) (gaugeV φ v) = v by
        have := gauge_gauge (-φ) v
        simpa [neg_neg] using this] at this
      rw [this]
      ext x
      simp [gaugeV]
    have := le_lamMax (θ + gradR φ) hw
    rw [magForm_gauge, nsq_gauge] at this
    exact this

/-- **The largest value depends only on the cyclic part.** -/
theorem lamMax_cyc (θ : Fin 40 → ℝ) : lamMax θ = lamMax (thetaCyc θ) := by
  conv_lhs => rw [theta_sub_cyc θ]
  exact lamMax_gauge _ _

/-! ## The lower bound -/

/-- **`λ_max(A_θ) ≥ 5 − ‖θ‖²/16`** for every `θ`, from the constant vector. -/
theorem lamMax_ge (θ : Fin 40 → ℝ) : 5 - sqL θ / 16 ≤ lamMax θ := by
  have hv : (fun _ : Fin 16 => (1 : ℂ)) ≠ 0 := fun h => by simpa using congrFun h 0
  have h := le_lamMax θ hv
  have hn : nsq (fun _ : Fin 16 => (1 : ℂ)) = 16 := by simp [nsq]
  have hf : magForm θ (fun _ => (1 : ℂ)) = ∑ l, 2 * Real.cos (θ l) := by
    simp only [magForm, star_one, mul_one, Complex.exp_ofReal_mul_I_re]
  rw [hn, hf] at h
  have hc : ∑ l, 2 * (1 - θ l ^ 2 / 2) ≤ ∑ l, 2 * Real.cos (θ l) :=
    Finset.sum_le_sum fun l _ => by nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ l)]
  have hs : ∑ l : Fin 40, 2 * (1 - θ l ^ 2 / 2) = 80 - sqL θ := by
    simp only [sqL, mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun l _ => show 2 * (θ l ^ 2 / 2) = θ l ^ 2 by ring]
    norm_num
  linarith


/-! ## The Clebsch bound on functions of mean zero -/

/-- The adjacency of the vertices over `ℂ`. -/
noncomputable def adjC : Matrix (Fin 16) (Fin 16) ℂ := Matrix.of fun x z => (adjZ x z : ℂ)

/-- The all-ones matrix. -/
def onesC : Matrix (Fin 16) (Fin 16) ℂ := Matrix.of fun _ _ => 1

theorem adjC_conjTranspose : adjCᴴ = adjC := by
  ext x z
  simp only [Matrix.conjTranspose_apply, adjC, Matrix.of_apply, star_intCast]
  rw [adj_symm]

theorem adjC_sq : adjC * adjC = (3 : ℂ) • 1 - (2 : ℂ) • adjC + (2 : ℂ) • onesC := by
  ext x y
  have h := congrArg (fun z : ℤ => (z : ℂ)) (adj_srg x y)
  push_cast at h
  simp only [Matrix.mul_apply, adjC, Matrix.of_apply, onesC, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [h]
  split_ifs <;> ring

theorem one_sub_adjC_sq :
    (1 - adjC)ᴴ * (1 - adjC) = (4 : ℂ) • (1 - adjC) + (2 : ℂ) • onesC := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, adjC_conjTranspose]
  have h : (1 - adjC) * (1 - adjC) = 1 - (2 : ℂ) • adjC + adjC * adjC := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    module
  rw [h, adjC_sq]
  module

theorem onesC_mulVec (y : Fin 16 → ℂ) (hy : ∑ x, y x = 0) : onesC *ᵥ y = 0 := by
  ext x
  simp [onesC, Matrix.mulVec, dotProduct, hy]

theorem re_star_self (w : Fin 16 → ℂ) : (star w ⬝ᵥ w).re = nsq w := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, nsq]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **On functions of mean zero the adjacency is at most one:** `Re y†Ay ≤ ‖y‖²`, since
`y†(1 − A)y = ‖(1 − A)y‖²/4` there (`(1 − A)² = 4(1 − A) + 2J`). -/
theorem clebsch_le (y : Fin 16 → ℂ) (hy : ∑ x, y x = 0) :
    (star y ⬝ᵥ (adjC *ᵥ y)).re ≤ nsq y := by
  set w := (1 - adjC) *ᵥ y
  have hw : star w ⬝ᵥ w = (4 : ℂ) * (star y ⬝ᵥ ((1 - adjC) *ᵥ y)) := by
    simp only [w]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, one_sub_adjC_sq,
      Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, onesC_mulVec y hy, smul_zero,
      add_zero, dotProduct_smul, smul_eq_mul]
  have hnn : 0 ≤ (star w ⬝ᵥ w).re := by rw [re_star_self]; exact nsq_nonneg w
  rw [hw, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at hnn
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im] at hnn
  norm_num at hnn
  rw [re_star_self] at hnn
  linarith

/-- One link's share of `y†Ay`. -/
theorem link_pair_sum (l : Fin 40) (y : Fin 16 → ℂ) :
    ∑ x, ∑ z, star (y x) * (linkInd l x z : ℂ) * y z =
      star (y (linkV l)) * y (linkU l) + star (y (linkU l)) * y (linkV l) := by
  simp only [linkInd]
  push_cast
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- The form at zero phases is the adjacency's form. -/
theorem magForm_zero_eq (y : Fin 16 → ℂ) : magForm 0 y = (star y ⬝ᵥ (adjC *ᵥ y)).re := by
  have hA : ∀ x z, adjC x z = ∑ l, (linkInd l x z : ℂ) := by
    intro x z
    simp only [adjC, Matrix.of_apply]
    rw [adjZ_links]
    push_cast
    rfl
  have hl : star y ⬝ᵥ (adjC *ᵥ y) =
      ∑ l, (star (y (linkV l)) * y (linkU l) + star (y (linkU l)) * y (linkV l)) := by
    have e : star y ⬝ᵥ (adjC *ᵥ y) = ∑ x, ∑ z, star (y x) * adjC x z * y z := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
    calc star y ⬝ᵥ (adjC *ᵥ y) = ∑ x : Fin 16, ∑ z : Fin 16, ∑ l : Fin 40,
          star (y x) * (linkInd l x z : ℂ) * y z := by
          rw [e]
          simp only [hA, Finset.mul_sum, Finset.sum_mul]
      _ = ∑ x : Fin 16, ∑ l : Fin 40, ∑ z : Fin 16, star (y x) * (linkInd l x z : ℂ) * y z := by
          refine Finset.sum_congr rfl fun x _ => ?_
          exact Finset.sum_comm
      _ = ∑ l : Fin 40, ∑ x : Fin 16, ∑ z : Fin 16, star (y x) * (linkInd l x z : ℂ) * y z :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => link_pair_sum l y
  rw [hl, Complex.re_sum, magForm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
    Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-! ## The mean and the rest -/

theorem split_term (e m a b : ℂ) :
    2 * (e * star (m + a) * (m + b)).re =
      Complex.normSq m * (2 * e.re) + 2 * (star m * (e * b + star e * a)).re +
        2 * (e * star a * b).re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- **The form split into the mean and the rest.** -/
theorem magForm_split (θ : Fin 40 → ℝ) (m : ℂ) (y : Fin 16 → ℂ) :
    magForm θ (fun x => m + y x) =
      Complex.normSq m * (∑ l, 2 * Real.cos (θ l)) +
        2 * (star m * ∑ l, (exp (θ l * I) * y (linkU l) + exp (-(θ l * I)) * y (linkV l))).re +
        magForm θ y := by
  have h1 : ∀ l, 2 * (exp (θ l * I) * star (m + y (linkV l)) * (m + y (linkU l))).re =
      Complex.normSq m * (2 * Real.cos (θ l)) +
        2 * (star m * (exp (θ l * I) * y (linkU l) + exp (-(θ l * I)) * y (linkV l))).re +
        2 * (exp (θ l * I) * star (y (linkV l)) * y (linkU l)).re := by
    intro l
    rw [split_term, Complex.exp_ofReal_mul_I_re, star_exp_real]
  have h2 : 2 * (star m * ∑ l, (exp (θ l * I) * y (linkU l) + exp (-(θ l * I)) * y (linkV l))).re =
      ∑ l, 2 * (star m * (exp (θ l * I) * y (linkU l) + exp (-(θ l * I)) * y (linkV l))).re := by
    rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  simp only [magForm]
  rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, h2]

theorem nsq_split (m : ℂ) (y : Fin 16 → ℂ) (hy : ∑ x, y x = 0) :
    nsq (fun x => m + y x) = 16 * Complex.normSq m + nsq y := by
  have h : ∀ x, Complex.normSq (m + y x) =
      Complex.normSq m + 2 * (star m * y x).re + Complex.normSq (y x) := by
    intro x
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  simp only [nsq, h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have h0 : ∑ x, 2 * (star m * y x).re = 0 := by
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.mul_sum, hy, mul_zero, Complex.zero_re,
      mul_zero]
  rw [h0]
  ring

/-- The sum over the links of a complex function of the head and of the tail. -/
theorem sum_ends_c (f : Fin 16 → ℂ) : ∑ l, (f (linkV l) + f (linkU l)) = 5 * ∑ x, f x := by
  have h : ∀ l, f (linkV l) + f (linkU l) =
      ∑ x, f x * (((if linkV l = x then 1 else 0) + (if linkU l = x then 1 else 0) : ℤ) : ℂ) := by
    intro l
    push_cast
    simp only [mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  rw [Finset.sum_congr rfl fun l _ => h l, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, ← Int.cast_sum, ends_count x]
  push_cast
  ring

/-- `Σ_ℓ ψ_ℓ (y_V − y_U) = Σ_x y_x (div ψ)_x`. -/
theorem sum_link_div (ψ : Fin 40 → ℝ) (y : Fin 16 → ℂ) :
    ∑ l, (ψ l : ℂ) * (y (linkV l) - y (linkU l)) = ∑ x, y x * (divR ψ x : ℂ) := by
  simp only [divR]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [incZ]
  push_cast
  simp only [sub_mul, ite_mul, one_mul, zero_mul, mul_sub, mul_ite, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- **The cross term of a field without divergence on a function of mean zero is of second order.**
-/
theorem cross_term_le (ψ : Fin 40 → ℝ) (hdiv : ∀ x, divR ψ x = 0) (hψ : ∀ l, |ψ l| ≤ 1)
    (y : Fin 16 → ℂ) (hy : ∑ x, y x = 0) :
    ‖∑ l, (exp (ψ l * I) * y (linkU l) + exp (-(ψ l * I)) * y (linkV l))‖ ≤
      ∑ l, ψ l ^ 2 * (‖y (linkU l)‖ + ‖y (linkV l)‖) := by
  have h5 : ∑ l, (y (linkV l) + y (linkU l)) = 0 := by rw [sum_ends_c, hy, mul_zero]
  have hd : ∑ l, (ψ l : ℂ) * (y (linkV l) - y (linkU l)) = 0 := by
    rw [sum_link_div]
    simp [hdiv]
  have heq : ∑ l, (exp (ψ l * I) * y (linkU l) + exp (-(ψ l * I)) * y (linkV l)) =
      ∑ l, ((exp (ψ l * I) - 1 - ψ l * I) * y (linkU l) +
        (exp (-(ψ l * I)) - 1 - (-(ψ l * I))) * y (linkV l)) := by
    have : ∑ l, ((exp (ψ l * I) - 1 - ψ l * I) * y (linkU l) +
        (exp (-(ψ l * I)) - 1 - (-(ψ l * I))) * y (linkV l)) =
        ∑ l, (exp (ψ l * I) * y (linkU l) + exp (-(ψ l * I)) * y (linkV l)) -
          ∑ l, (y (linkV l) + y (linkU l)) + I * ∑ l, (ψ l : ℂ) * (y (linkV l) - y (linkU l)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [this, h5, hd]
    ring
  rw [heq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  have hz1 : ‖(ψ l : ℂ) * I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hψ l
  have hz2 : ‖-((ψ l : ℂ) * I)‖ ≤ 1 := by rw [norm_neg]; exact hz1
  have e1 := Complex.norm_exp_sub_one_sub_id_le hz1
  have e2 := Complex.norm_exp_sub_one_sub_id_le hz2
  have hn : ‖(ψ l : ℂ) * I‖ ^ 2 = ψ l ^ 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [norm_neg, hn] at e2
  rw [hn] at e1
  calc ‖(exp (ψ l * I) - 1 - ψ l * I) * y (linkU l) +
        (exp (-(ψ l * I)) - 1 - (-(ψ l * I))) * y (linkV l)‖
      ≤ ‖(exp (ψ l * I) - 1 - ψ l * I) * y (linkU l)‖ +
          ‖(exp (-(ψ l * I)) - 1 - (-(ψ l * I))) * y (linkV l)‖ := norm_add_le _ _
    _ = ‖exp (ψ l * I) - 1 - ψ l * I‖ * ‖y (linkU l)‖ +
          ‖exp (-(ψ l * I)) - 1 - (-(ψ l * I))‖ * ‖y (linkV l)‖ := by rw [norm_mul, norm_mul]
    _ ≤ ψ l ^ 2 * ‖y (linkU l)‖ + ψ l ^ 2 * ‖y (linkV l)‖ := by
        gcongr
    _ = ψ l ^ 2 * (‖y (linkU l)‖ + ‖y (linkV l)‖) := by ring

/-- **A small phase moves the form of a function of mean zero by little.** -/
theorem magForm_rest_le (ψ : Fin 40 → ℝ) (c : ℝ) (hψ : ∀ l, |ψ l| ≤ c) (y : Fin 16 → ℂ)
    (hy : ∑ x, y x = 0) : magForm ψ y ≤ (1 + 5 * c) * nsq y := by
  have hc : 0 ≤ c := le_trans (abs_nonneg _) (hψ 0)
  have h0 := clebsch_le y hy
  rw [← magForm_zero_eq] at h0
  have hdiff : magForm ψ y - magForm 0 y ≤
      c * ∑ l, (Complex.normSq (y (linkV l)) + Complex.normSq (y (linkU l))) := by
    simp only [magForm, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    have hre : 2 * (exp (ψ l * I) * star (y (linkV l)) * y (linkU l)).re -
        2 * (star (y (linkV l)) * y (linkU l)).re =
        2 * ((exp (ψ l * I) - 1) * star (y (linkV l)) * y (linkU l)).re := by
      rw [show (exp (ψ l * I) - 1) * star (y (linkV l)) * y (linkU l) =
          exp (ψ l * I) * star (y (linkV l)) * y (linkU l) - star (y (linkV l)) * y (linkU l) by
            ring,
        Complex.sub_re]
      ring
    rw [hre]
    have hb : ‖exp (ψ l * I) - 1‖ ≤ c := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := ψ l)
      rw [mul_comm] at this
      rw [Real.norm_eq_abs] at this
      exact this.trans (hψ l)
    have h1 : ((exp (ψ l * I) - 1) * star (y (linkV l)) * y (linkU l)).re ≤
        c * (‖y (linkV l)‖ * ‖y (linkU l)‖) := by
      calc _ ≤ ‖(exp (ψ l * I) - 1) * star (y (linkV l)) * y (linkU l)‖ := Complex.re_le_norm _
        _ = ‖exp (ψ l * I) - 1‖ * (‖y (linkV l)‖ * ‖y (linkU l)‖) := by
          rw [norm_mul, norm_mul, norm_star]; ring
        _ ≤ c * (‖y (linkV l)‖ * ‖y (linkU l)‖) := by gcongr
    have h2 : 2 * (‖y (linkV l)‖ * ‖y (linkU l)‖) ≤
        Complex.normSq (y (linkV l)) + Complex.normSq (y (linkU l)) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      nlinarith [sq_nonneg (‖y (linkV l)‖ - ‖y (linkU l)‖)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hc]
  rw [show ∑ l, (Complex.normSq (y (linkV l)) + Complex.normSq (y (linkU l))) = 5 * nsq y by
    rw [nsq]; exact sum_ends fun x => Complex.normSq (y x)] at hdiff
  nlinarith

/-- `|ψ_ℓ| ≤ √‖ψ‖²`. -/
theorem abs_le_sqrt_sqL (ψ : Fin 40 → ℝ) (l : Fin 40) : |ψ l| ≤ Real.sqrt (sqL ψ) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun m _ => sq_nonneg (ψ m)) (Finset.mem_univ l))

theorem norm_le_sqrt_nsq (y : Fin 16 → ℂ) (x : Fin 16) : ‖y x‖ ≤ Real.sqrt (nsq y) := by
  rw [← Real.sqrt_sq (norm_nonneg (y x))]
  apply Real.sqrt_le_sqrt
  rw [← Complex.normSq_eq_norm_sq]
  exact Finset.single_le_sum (fun z _ => Complex.normSq_nonneg (y z)) (Finset.mem_univ x)

/-- **The quadratic estimate of a two-by-two form.** -/
theorem two_by_two (a b d M S t : ℝ) (hb : 0 ≤ b) (hp : 0 ≤ M - a) (hq : 0 ≤ M - d)
    (hdisc : b ^ 2 ≤ 4 * (M - a) * (M - d)) (_hS : 0 ≤ S) (_ht : 0 ≤ t) :
    a * S ^ 2 + b * S * t + d * t ^ 2 ≤ M * (S ^ 2 + t ^ 2) := by
  rcases eq_or_lt_of_le hp with h0 | hpos
  · have hb0 : b = 0 := by nlinarith
    subst hb0
    nlinarith
  · have key : 0 ≤ 4 * (M - a) * ((M - a) * S ^ 2 - b * S * t + (M - d) * t ^ 2) := by
      nlinarith [sq_nonneg (2 * (M - a) * S - b * t),
        mul_nonneg (sub_nonneg.mpr hdisc) (sq_nonneg t)]
    have : 0 ≤ (M - a) * S ^ 2 - b * S * t + (M - d) * t ^ 2 := by
      by_contra hneg
      have hneg' := lt_of_not_ge hneg
      nlinarith
    nlinarith [mul_nonneg hb (mul_nonneg _hS _ht)]

/-- **The upper bound:** for phases without divergence and `‖ψ‖² ≤ 1/100`,
`v†A_ψv ≤ (5 − ‖ψ‖²/16 + ‖ψ‖⁴/10)‖v‖²`. -/
theorem magForm_upper (ψ : Fin 40 → ℝ) (hdiv : ∀ x, divR ψ x = 0) (hsmall : sqL ψ ≤ 1 / 100)
    (v : Fin 16 → ℂ) : magForm ψ v ≤ (5 - sqL ψ / 16 + sqL ψ ^ 2 / 10) * nsq v := by
  have hsq0 : 0 ≤ sqL ψ := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hc : Real.sqrt (sqL ψ) ≤ 1 / 10 := by
    rw [show (1 / 10 : ℝ) = Real.sqrt (1 / 100) by
      rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hsmall
  have hψ1 : ∀ l, |ψ l| ≤ 1 / 10 := fun l => (abs_le_sqrt_sqL ψ l).trans hc
  set m : ℂ := (∑ x, v x) / 16
  set y : Fin 16 → ℂ := fun x => v x - m
  have hy : ∑ x, y x = 0 := by
    simp only [y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, m]
    push_cast
    ring
  have hv : v = fun x => m + y x := by ext x; simp [y]
  -- the three pieces
  have hcos : ∑ l, 2 * Real.cos (ψ l) ≤ 80 - sqL ψ + 5 / 48 * sqL ψ ^ 2 := by
    have hb : ∀ l, 2 * Real.cos (ψ l) ≤ 2 - ψ l ^ 2 + 5 / 48 * ψ l ^ 2 * sqL ψ := by
      intro l
      have h1 := Real.cos_bound (x := ψ l) ((hψ1 l).trans (by norm_num))
      have h4 : |ψ l| ^ 4 = ψ l ^ 2 * ψ l ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs]; ring
      have hle : ψ l ^ 2 ≤ sqL ψ :=
        Finset.single_le_sum (fun m _ => sq_nonneg (ψ m)) (Finset.mem_univ l)
      rw [h4] at h1
      have := (abs_le.mp h1).2
      nlinarith [mul_le_mul_of_nonneg_left hle (sq_nonneg (ψ l))]
    calc ∑ l, 2 * Real.cos (ψ l) ≤ ∑ l, (2 - ψ l ^ 2 + 5 / 48 * ψ l ^ 2 * sqL ψ) :=
          Finset.sum_le_sum fun l _ => hb l
      _ = 80 - sqL ψ + 5 / 48 * sqL ψ ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
          simp only [sqL]
          ring
  set t := Real.sqrt (nsq y)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htt : t ^ 2 = nsq y := Real.sq_sqrt (nsq_nonneg y)
  have hcross : 2 * (star m * ∑ l, (exp (ψ l * I) * y (linkU l) +
      exp (-(ψ l * I)) * y (linkV l))).re ≤ 2 * ‖m‖ * (2 * sqL ψ * t) := by
    have h1 := cross_term_le ψ hdiv (fun l => (hψ1 l).trans (by norm_num)) y hy
    have h2 : ∑ l, ψ l ^ 2 * (‖y (linkU l)‖ + ‖y (linkV l)‖) ≤ 2 * sqL ψ * t := by
      calc ∑ l, ψ l ^ 2 * (‖y (linkU l)‖ + ‖y (linkV l)‖) ≤ ∑ l, ψ l ^ 2 * (2 * t) :=
            Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
              (by linarith [norm_le_sqrt_nsq y (linkU l), norm_le_sqrt_nsq y (linkV l)])
              (sq_nonneg _)
        _ = 2 * sqL ψ * t := by rw [sqL, ← Finset.sum_mul]; ring
    calc 2 * (star m * _).re ≤ 2 * ‖star m * ∑ l, (exp (ψ l * I) * y (linkU l) +
          exp (-(ψ l * I)) * y (linkV l))‖ := by
          gcongr
          exact Complex.re_le_norm _
      _ = 2 * ‖m‖ * ‖∑ l, (exp (ψ l * I) * y (linkU l) + exp (-(ψ l * I)) * y (linkV l))‖ := by
          rw [norm_mul, norm_star]; ring
      _ ≤ 2 * ‖m‖ * (2 * sqL ψ * t) := by
          gcongr
          exact h1.trans h2
  have hrest := magForm_rest_le ψ (1 / 10) hψ1 y hy
  have hsplit := magForm_split ψ m y
  have hnsq := nsq_split m y hy
  rw [hv, hsplit, hnsq]
  set S := 4 * ‖m‖
  have hS0 : 0 ≤ S := by positivity
  have hSS : S ^ 2 = 16 * Complex.normSq m := by
    simp only [S]
    rw [Complex.normSq_eq_norm_sq]
    ring
  have hnm : 0 ≤ Complex.normSq m := Complex.normSq_nonneg m
  have key := two_by_two (5 - sqL ψ / 16 + 5 / 768 * sqL ψ ^ 2) (sqL ψ) (3 / 2)
    (5 - sqL ψ / 16 + sqL ψ ^ 2 / 10) S t hsq0 (by nlinarith) (by nlinarith) (by nlinarith) hS0 ht0
  have e1 : Complex.normSq m * (∑ l, 2 * Real.cos (ψ l)) ≤
      (5 - sqL ψ / 16 + 5 / 768 * sqL ψ ^ 2) * S ^ 2 := by
    rw [hSS]
    nlinarith [mul_le_mul_of_nonneg_left hcos hnm]
  have e2 : 2 * ‖m‖ * (2 * sqL ψ * t) = sqL ψ * S * t := by simp only [S]; ring
  have e3 : magForm ψ y ≤ 3 / 2 * t ^ 2 := by rw [htt]; linarith
  rw [← hSS, ← htt]
  nlinarith

/-- **`λ_max(A_ψ) ≤ 5 − ‖ψ‖²/16 + ‖ψ‖⁴/10`** for phases without divergence, `‖ψ‖² ≤ 1/100`. -/
theorem lamMax_upper (ψ : Fin 40 → ℝ) (hdiv : ∀ x, divR ψ x = 0) (hsmall : sqL ψ ≤ 1 / 100) :
    lamMax ψ ≤ 5 - sqL ψ / 16 + sqL ψ ^ 2 / 10 :=
  lamMax_le ψ _ fun v _ => magForm_upper ψ hdiv hsmall v

/-! ## The long-range zero -/

/-- **The long-range zero** under the phases: the root `u_c = (λ − √(λ² − 16))/8` of
`1 + 4u² = uλ_max`. -/
noncomputable def ucrit (θ : Fin 40 → ℝ) : ℝ := (lamMax θ - Real.sqrt (lamMax θ ^ 2 - 16)) / 8

theorem ucrit_root (θ : Fin 40 → ℝ) (h4 : 4 ≤ lamMax θ) :
    1 + 4 * ucrit θ ^ 2 = ucrit θ * lamMax θ := by
  have hr := Real.sq_sqrt (show 0 ≤ lamMax θ ^ 2 - 16 by nlinarith)
  unfold ucrit
  linear_combination (1 / 16) * hr

/-- **The logarithm of the root:** `|log((λ − √(λ² − 16))/2) − (5 − λ)/3| ≤ (5 − λ)²/2` for
`9/2 ≤ λ ≤ 5`. -/
theorem log_root_bound (lam : ℝ) (h1 : 9 / 2 ≤ lam) (h2 : lam ≤ 5) :
    |Real.log ((lam - Real.sqrt (lam ^ 2 - 16)) / 2) - (5 - lam) / 3| ≤ (5 - lam) ^ 2 / 2 := by
  set ε := 5 - lam with hε
  have hε0 : 0 ≤ ε := by linarith
  have hε1 : ε ≤ 1 / 2 := by linarith
  have hlam : lam = 5 - ε := by linarith
  have hr_up : Real.sqrt (lam ^ 2 - 16) ≤ 3 - 5 * ε / 3 := by
    calc Real.sqrt (lam ^ 2 - 16) ≤ Real.sqrt ((3 - 5 * ε / 3) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [hlam]; nlinarith)
      _ = 3 - 5 * ε / 3 := Real.sqrt_sq (by linarith)
  have hr_lo : 3 - 5 * ε / 3 - ε ^ 2 ≤ Real.sqrt (lam ^ 2 - 16) := by
    calc 3 - 5 * ε / 3 - ε ^ 2 = Real.sqrt ((3 - 5 * ε / 3 - ε ^ 2) ^ 2) :=
          (Real.sqrt_sq (by nlinarith)).symm
      _ ≤ Real.sqrt (lam ^ 2 - 16) := Real.sqrt_le_sqrt (by
          rw [hlam]
          nlinarith [mul_nonneg hε0 hε0, mul_nonneg (mul_nonneg hε0 hε0) hε0,
            mul_nonneg (mul_nonneg hε0 hε0) (mul_nonneg hε0 hε0)])
  set x := (lam - Real.sqrt (lam ^ 2 - 16)) / 2 with hx
  have hx_lo : 1 + ε / 3 ≤ x := by rw [hx]; linarith
  have hx_up : x ≤ 1 + ε / 3 + ε ^ 2 / 2 := by rw [hx]; linarith
  have hxpos : 0 < x := by linarith
  have hlog_up : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hxpos
  have hlog_lo : 1 - x⁻¹ ≤ Real.log x := Real.one_sub_inv_le_log_of_pos hxpos
  have hinv : (x - 1) - (x - 1) ^ 2 ≤ 1 - x⁻¹ := by
    have e : 1 - x⁻¹ = (x - 1) / x := by field_simp
    rw [e, le_div_iff₀ hxpos]
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) (show 0 ≤ x - 1 by linarith)]
  have hmono : ε / 3 - ε ^ 2 / 9 ≤ (x - 1) - (x - 1) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ x - 1 - ε / 3 by linarith)
      (show 0 ≤ 1 - (x - 1) - ε / 3 by nlinarith)]
  rw [abs_le]
  constructor <;> nlinarith

/-- **The long-range zero under a circulation on the links:** with `θ_cyc` the part of the phases
that no gauge transformation removes and `‖θ_cyc‖² ≤ 1/100`,
`|λ_max(A_θ) − (5 − ‖θ_cyc‖²/16)| ≤ ‖θ_cyc‖⁴/10`, `1 + 4u_c² = u_c λ_max(A_θ)` and
`|log 4u_c − ‖θ_cyc‖²/48| ≤ ‖θ_cyc‖⁴/20`: `log 4u_c = ‖θ_cyc‖²/48 + O(θ⁴)`. -/
theorem long_range_zero (θ : Fin 40 → ℝ) (hθ : sqL (thetaCyc θ) ≤ 1 / 100) :
    |lamMax θ - (5 - sqL (thetaCyc θ) / 16)| ≤ sqL (thetaCyc θ) ^ 2 / 10 ∧
    1 + 4 * ucrit θ ^ 2 = ucrit θ * lamMax θ ∧
    |Real.log (4 * ucrit θ) - sqL (thetaCyc θ) / 48| ≤ sqL (thetaCyc θ) ^ 2 / 20 := by
  set s := sqL (thetaCyc θ)
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hlo : 5 - s / 16 ≤ lamMax θ := by
    rw [lamMax_cyc]
    exact lamMax_ge _
  have hup : lamMax θ ≤ 5 - s / 16 + s ^ 2 / 10 := by
    rw [lamMax_cyc]
    exact lamMax_upper _ (divR_thetaCyc θ) hθ
  have h5 : lamMax θ ≤ 5 := lamMax_le_five θ
  have hlam : 9 / 2 ≤ lamMax θ := by nlinarith
  refine ⟨?_, ucrit_root θ (by linarith), ?_⟩
  · rw [abs_le]
    constructor <;> nlinarith
  · have h4u : 4 * ucrit θ = (lamMax θ - Real.sqrt (lamMax θ ^ 2 - 16)) / 2 := by
      unfold ucrit
      ring
    rw [h4u]
    have hb := log_root_bound (lamMax θ) hlam h5
    have hε : (5 - lamMax θ) ^ 2 ≤ (s / 16) ^ 2 := by
      have : 0 ≤ 5 - lamMax θ := by linarith
      have : 5 - lamMax θ ≤ s / 16 := by linarith
      nlinarith
    rw [abs_le] at hb ⊢
    obtain ⟨hb1, hb2⟩ := hb
    constructor <;> nlinarith


/-! ## `lamMax` is the largest eigenvalue of the step with phases -/

/-- **The step with phases on the links** `A_θ`: `e^{iθ_ℓ}` from `U_ℓ` to `V_ℓ`, `e^{−iθ_ℓ}` back.
-/
noncomputable def magAdj (θ : Fin 40 → ℝ) : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun x z => ∑ l,
    ((if x = linkV l then (if z = linkU l then exp (θ l * I) else 0) else 0) +
      (if x = linkU l then (if z = linkV l then exp (-(θ l * I)) else 0) else 0))

theorem magAdj_isHermitian (θ : Fin 40 → ℝ) : (magAdj θ).IsHermitian := by
  ext x z
  simp only [Matrix.conjTranspose_apply, magAdj, Matrix.of_apply, star_sum, star_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e1 : star (exp ((θ l : ℂ) * I)) = exp (-((θ l : ℂ) * I)) := star_exp_real (θ l)
  have e2 : star (exp (-((θ l : ℂ) * I))) = exp ((θ l : ℂ) * I) := by
    rw [← e1, star_star]
  have hne : linkU l ≠ linkV l := (links_ok l).1.ne
  by_cases h1 : z = linkV l <;> by_cases h2 : x = linkU l <;> by_cases h3 : z = linkU l <;>
    by_cases h4 : x = linkV l <;> simp_all [add_comm, hne.symm]

/-- One link's share of `v†A_θv`. -/
theorem link_pair_sum_phase (θ : Fin 40 → ℝ) (l : Fin 40) (v : Fin 16 → ℂ) :
    ∑ x, ∑ z, star (v x) *
      ((if x = linkV l then (if z = linkU l then exp (θ l * I) else 0) else 0) +
        (if x = linkU l then (if z = linkV l then exp (-(θ l * I)) else 0) else 0)) * v z =
      star (v (linkV l)) * exp (θ l * I) * v (linkU l) +
        star (v (linkU l)) * exp (-(θ l * I)) * v (linkV l) := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **The form of the matrix is the link sum:** `Re v†A_θv = magForm θ v`. -/
theorem magForm_eq (θ : Fin 40 → ℝ) (v : Fin 16 → ℂ) :
    (star v ⬝ᵥ (magAdj θ *ᵥ v)).re = magForm θ v := by
  have hl : star v ⬝ᵥ (magAdj θ *ᵥ v) = ∑ l, (star (v (linkV l)) * exp (θ l * I) * v (linkU l) +
      star (v (linkU l)) * exp (-(θ l * I)) * v (linkV l)) := by
    calc star v ⬝ᵥ (magAdj θ *ᵥ v) = ∑ x : Fin 16, ∑ z : Fin 16, ∑ l : Fin 40, star (v x) *
          ((if x = linkV l then (if z = linkU l then exp (θ l * I) else 0) else 0) +
            (if x = linkU l then (if z = linkV l then exp (-(θ l * I)) else 0) else 0)) * v z := by
          simp only [dotProduct, Matrix.mulVec, magAdj, Matrix.of_apply, Pi.star_apply,
            Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = ∑ x : Fin 16, ∑ l : Fin 40, ∑ z : Fin 16, star (v x) *
          ((if x = linkV l then (if z = linkU l then exp (θ l * I) else 0) else 0) +
            (if x = linkU l then (if z = linkV l then exp (-(θ l * I)) else 0) else 0)) * v z := by
          refine Finset.sum_congr rfl fun x _ => ?_
          exact Finset.sum_comm
      _ = ∑ l : Fin 40, ∑ x : Fin 16, ∑ z : Fin 16, star (v x) *
          ((if x = linkV l then (if z = linkU l then exp (θ l * I) else 0) else 0) +
            (if x = linkU l then (if z = linkV l then exp (-(θ l * I)) else 0) else 0)) * v z :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => link_pair_sum_phase θ l v
  rw [hl, Complex.re_sum, magForm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e : star (v (linkU l)) * exp (-(θ l * I)) * v (linkV l) =
      star (star (v (linkV l)) * exp (θ l * I) * v (linkU l)) := by
    rw [star_mul', star_mul', star_star, star_exp_real]
    ring
  rw [Complex.add_re, e, Complex.star_def, Complex.conj_re]
  ring_nf

theorem star_self_re (v : Fin 16 → ℂ) : (star v ⬝ᵥ v).re = nsq v := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, nsq]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **Every eigenvalue of `A_θ` is at most `lamMax θ`.** -/
theorem eigen_le_lamMax (θ : Fin 40 → ℝ) (μ : ℂ) (v : Fin 16 → ℂ) (hv : v ≠ 0)
    (h : magAdj θ *ᵥ v = μ • v) : μ.re ≤ lamMax θ := by
  have hq := le_lamMax θ hv
  rw [← magForm_eq, h, dotProduct_smul, smul_eq_mul] at hq
  have hreal : (star v ⬝ᵥ v).im = 0 := by
    simp only [dotProduct, Pi.star_apply, Complex.im_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [Complex.mul_re, hreal, mul_zero, sub_zero, star_self_re] at hq
  exact le_of_mul_le_mul_right hq (nsq_pos hv)

theorem rayleigh_euclid (θ : Fin 40 → ℝ) (x : EuclideanSpace ℂ (Fin 16)) :
    RCLike.re (inner ℂ (Matrix.toEuclideanLin (magAdj θ) x) x) / ‖x‖ ^ 2 =
      magForm θ (WithLp.ofLp x) / nsq (WithLp.ofLp x) := by
  congr 1
  · have e : inner ℂ (Matrix.toEuclideanLin (magAdj θ) x) x =
        star (star (WithLp.ofLp x) ⬝ᵥ (magAdj θ *ᵥ WithLp.ofLp x)) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
        dotProduct_comm, Matrix.star_dotProduct]
    rw [e, ← magForm_eq, RCLike.re_to_complex, Complex.star_def, Complex.conj_re]
  · rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), nsq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq]

/-- The vectors and the Euclidean vectors, nonzero ones to nonzero ones. -/
def toEuclidNZ (v : {v : Fin 16 → ℂ // v ≠ 0}) : {x : EuclideanSpace ℂ (Fin 16) // x ≠ 0} :=
  ⟨WithLp.toLp 2 v.1, fun h => v.2 (by simpa using congrArg WithLp.ofLp h)⟩

theorem toEuclidNZ_surjective : Function.Surjective toEuclidNZ := by
  intro x
  refine ⟨⟨WithLp.ofLp x.1, fun h => x.2 (by simpa using congrArg (WithLp.toLp 2) h)⟩, ?_⟩
  simp [toEuclidNZ]

/-- **`lamMax θ` is the supremum of the Rayleigh quotient of `A_θ` on the Euclidean space.** -/
theorem lamMax_eq_rayleigh (θ : Fin 40 → ℝ) :
    lamMax θ = ⨆ x : {x : EuclideanSpace ℂ (Fin 16) // x ≠ 0},
      RCLike.re (inner ℂ (Matrix.toEuclideanLin (magAdj θ) x) (x : EuclideanSpace ℂ (Fin 16))) /
        ‖(x : EuclideanSpace ℂ (Fin 16))‖ ^ 2 := by
  rw [lamMax, ← toEuclidNZ_surjective.iSup_comp]
  congr 1
  ext v
  rw [rayleigh_euclid]
  rfl

/-- **`lamMax θ` is an eigenvalue of `A_θ`**, and by `eigen_le_lamMax` the largest:
`λ_max(A_θ)`. -/
theorem lamMax_hasEigenvalue (θ : Fin 40 → ℝ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin (magAdj θ)) (lamMax θ : ℂ) := by
  rw [lamMax_eq_rayleigh]
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (magAdj_isHermitian θ)).hasEigenvalue_iSup_of_finiteDimensional

end Comparison.WholePicture

end
