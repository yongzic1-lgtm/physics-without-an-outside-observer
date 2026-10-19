module

public import Comparison.Existence.Walk

/-!
# Book VII. At every vertex: closed facts, squares and the mass form (Propositions 32, 38, 39)

* `Connection`, `Connection.rename`, `hol`: a rotation `U x y` for each ordered pair of vertices with
  `U y x = (U x y)⁻¹`; a gauge transformation `g` turns it into `g x · U x y · (g y)⁻¹`; the holonomy of
  a walk `[x₀, x₁, …, x_n]` is `U x_n x_{n−1} ⋯ U x₁ x₀`.
* `hol_rename`: a gauge transformation turns the holonomy by the gauges at its two ends;
  `hol_rename_closed`: for a closed walk, by one rotation at its own vertex;
  `trace_hol_isFact`: the trace of a closed holonomy of matrices is unchanged by every gauge
  transformation; `open_transport_any`: the transport between two different vertices can be gauge-transformed into
  any rotation (Proposition 32).
* `four_cycles`, `card_squares`: every closed walk of four steps on the sixteen two-spinor states is a
  square `tsts`, and there are forty squares (Proposition 38).
* `massForm`: `M_D(X, Y) = Tr([X, P_D]ᵀ[Y, P_D])` on the real `n × n` matrices; `comm_symm`:
  `[X, P_D]` is symmetric for `X` antisymmetric; `massForm_self_eq`: `M_D(X, X)` is the sum of the
  squares of the entries of `[X, P_D]`; `massForm_nonneg`; `massForm_eq_zero_iff`: zero exactly on
  the kept rotations, `X θ_D = θ_D X`; `massForm_unit_moved`: `2` on every unit moved rotation
  `E_ab − E_ba`, `a ∈ D`, `b ∉ D`; `massForm_unit_kept`: `0` on the unit kept rotations (Prop. 39).
-/

@[expose] public section

namespace Comparison

open Matrix hiding J

/-! ## Closed facts -/

/-- A connection: a rotation for each ordered pair of vertices, `U y x = (U x y)⁻¹`. -/
structure Connection (X G : Type*) [Group G] where
  U : X → X → G
  U_inv : ∀ x y, U y x = (U x y)⁻¹

variable {X G : Type*} [Group G]

/-- **A gauge transformation** `g`: `U x y ↦ g x · U x y · (g y)⁻¹`. -/
def Connection.rename (g : X → G) (c : Connection X G) : Connection X G :=
  ⟨fun x y => g x * c.U x y * (g y)⁻¹, by
    intro x y
    rw [c.U_inv]
    group⟩

/-- The holonomy of a walk `[x₀, x₁, …, x_n]`: `U x_n x_{n−1} ⋯ U x₁ x₀`. -/
def hol (c : Connection X G) : List X → G
  | [] => 1
  | [_] => 1
  | x :: y :: rest => hol c (y :: rest) * c.U y x

/-- **A gauge transformation turns a holonomy by the gauges at its two ends.** -/
theorem hol_rename (c : Connection X G) (g : X → G) (x : X) (rest : List X) :
    hol (c.rename g) (x :: rest) =
      g ((x :: rest).getLast (List.cons_ne_nil x rest)) * hol c (x :: rest) * (g x)⁻¹ := by
  induction rest generalizing x with
  | nil => simp [hol]
  | cons y rest ih =>
    have e1 : hol (c.rename g) (x :: y :: rest) =
        hol (c.rename g) (y :: rest) * (c.rename g).U y x := rfl
    have e2 : hol c (x :: y :: rest) = hol c (y :: rest) * c.U y x := rfl
    rw [e1, e2, ih y, List.getLast_cons_cons]
    simp only [Connection.rename]
    group

/-- **For a closed walk the holonomy is turned at its own vertex:**
`hol ↦ g x₀ · hol · (g x₀)⁻¹`. -/
theorem hol_rename_closed (c : Connection X G) (g : X → G) (x : X) (rest : List X)
    (hclosed : (x :: rest).getLast (List.cons_ne_nil x rest) = x) :
    hol (c.rename g) (x :: rest) = g x * hol c (x :: rest) * (g x)⁻¹ := by
  rw [hol_rename, hclosed]

/-- **The trace of a closed holonomy is a fact:** no gauge transformation changes it. -/
theorem trace_hol_isFact {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (c : Connection X (Matrix n n R)ˣ) (g : X → (Matrix n n R)ˣ) (x : X) (rest : List X)
    (hclosed : (x :: rest).getLast (List.cons_ne_nil x rest) = x) :
    ((hol (c.rename g) (x :: rest) : (Matrix n n R)ˣ) : Matrix n n R).trace =
      ((hol c (x :: rest) : (Matrix n n R)ˣ) : Matrix n n R).trace := by
  rw [hol_rename_closed c g x rest hclosed, Units.val_mul, Units.val_mul, Matrix.trace_units_conj]

/-- **An open transport can be gauge-transformed into any rotation:** a number that no gauge transformation changes
takes the same value at every rotation. -/
theorem open_transport_any (c : Connection X G) {x y : X} (hxy : x ≠ y) (V : G) :
    ∃ g : X → G, (c.rename g).U x y = V := by
  classical
  refine ⟨Function.update (fun _ => 1) x (V * (c.U x y)⁻¹), ?_⟩
  simp only [Connection.rename, Function.update_self, Function.update_of_ne (Ne.symm hxy), inv_one,
    mul_one, inv_mul_cancel_right]

/-! ## The squares of the sixteen two-spinor states (Proposition 38) -/

/-- **Every closed walk of four steps is a square `tsts`.** -/
theorem four_cycles :
    ∀ (x : Fin 16) (a b c d : Fin 5), a ≠ b → b ≠ c → c ≠ d → d ≠ a →
      transition d (transition c (transition b (transition a x))) = x → a = c ∧ b = d := by
  decide +kernel

/-- The square through the vertex `x` with the steps `s, t`: its four vertices. -/
def square (x : Fin 16) (s t : Fin 5) : Finset (Fin 16) :=
  {x, transition s x, transition t (transition s x), transition t x}

theorem square_closes (x : Fin 16) (s t : Fin 5) :
    transition t (transition s (transition t (transition s x))) = x := by
  revert x s t
  decide

/-- **Forty squares:** ten through each vertex, four vertices on each. -/
theorem card_squares :
    (Finset.image (fun p : Fin 16 × Fin 5 × Fin 5 => square p.1 p.2.1 p.2.2)
      (Finset.univ.filter fun p : Fin 16 × Fin 5 × Fin 5 => p.2.1 < p.2.2)).card = 40 := by
  decide +kernel

/-! ## The mass form (Proposition 39) -/

variable {n : ℕ}

/-- The projector onto the divided part `D`. -/
def projD (D : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun a => if a ∈ D then 1 else 0

/-- The sign of the division: `θ_D = 1 − 2 P_D`. -/
def thetaD (D : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun a => if a ∈ D then -1 else 1

/-- **The mass form** `M_D(X, Y) = Tr([X, P_D]ᵀ [Y, P_D])`. -/
def massForm (D : Finset (Fin n)) (X Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ((X * projD D - projD D * X)ᵀ * (Y * projD D - projD D * Y)).trace

theorem thetaD_eq (D : Finset (Fin n)) : thetaD D = 1 - (2 : ℝ) • projD D := by
  ext i j
  simp only [thetaD, projD, Matrix.diagonal_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> norm_num

theorem projD_transpose (D : Finset (Fin n)) : (projD D)ᵀ = projD D := by
  rw [projD, Matrix.diagonal_transpose]

/-- **`[X, P_D]` is symmetric** for every antisymmetric `X`. -/
theorem comm_symm (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) (hX : Xᵀ = -X) :
    (X * projD D - projD D * X)ᵀ = X * projD D - projD D * X := by
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, projD_transpose, hX,
    Matrix.mul_neg, Matrix.neg_mul]
  abel

theorem comm_apply (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (X * projD D - projD D * X) i j =
      X i j * ((if j ∈ D then 1 else 0) - (if i ∈ D then 1 else 0)) := by
  simp only [projD, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- **`M_D(X, X)` is the sum of the squares of the entries of `[X, P_D]`.** -/
theorem massForm_self_eq (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) :
    massForm D X X = ∑ i, ∑ j, ((X * projD D - projD D * X) i j) ^ 2 := by
  rw [massForm, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The mass form is not negative. -/
theorem massForm_nonneg (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ massForm D X X := by
  rw [massForm_self_eq]
  positivity

/-- **The mass form vanishes exactly on the kept rotations:** `M_D(X, X) = 0 ⟺ X θ_D = θ_D X`. -/
theorem massForm_eq_zero_iff (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) :
    massForm D X X = 0 ↔ X * thetaD D = thetaD D * X := by
  rw [massForm_self_eq]
  have hsq : (∑ i, ∑ j, ((X * projD D - projD D * X) i j) ^ 2 = 0) ↔
      X * projD D - projD D * X = 0 := by
    constructor
    · intro h
      ext i j
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
        fun j _ => sq_nonneg ((X * projD D - projD D * X) i j))).mp h i (Finset.mem_univ i)
      have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
        sq_nonneg ((X * projD D - projD D * X) i j))).mp hi j (Finset.mem_univ j)
      simpa using hij
    · intro h
      simp only [h, Matrix.zero_apply]
      simp
  rw [hsq, thetaD_eq, mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  constructor
  · intro h
    rw [sub_eq_zero] at h
    rw [h]
  · intro h
    have h2 : (2 : ℝ) • (X * projD D) = (2 : ℝ) • (projD D * X) := by
      have := congrArg (fun M => X - M) h
      simp only [sub_sub_cancel] at this
      exact this
    have h3 := smul_right_injective (Matrix (Fin n) (Fin n) ℝ) (two_ne_zero) h2
    rw [h3, sub_self]

/-- The unit rotation of the plane `(a, b)`: `E_ab − E_ba`. -/
def unitTurn (a b : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (if i = a ∧ j = b then 1 else 0) - (if i = b ∧ j = a then 1 else 0)

theorem unitTurn_transpose (a b : Fin n) : (unitTurn a b)ᵀ = -unitTurn a b := by
  ext i j
  simp only [unitTurn, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply,
    and_comm (a := j = a), and_comm (a := j = b)]
  ring

/-- **Every unit moved rotation has mass two:** `M_D(E_ab − E_ba) = 2` for `a ∈ D`, `b ∉ D`. -/
theorem massForm_unit_moved (D : Finset (Fin n)) {a b : Fin n} (ha : a ∈ D) (hb : b ∉ D) :
    massForm D (unitTurn a b) (unitTurn a b) = 2 := by
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  have hpt : ∀ i j, ((unitTurn a b * projD D - projD D * unitTurn a b) i j) ^ 2 =
      (if i = a ∧ j = b then 1 else 0) + (if i = b ∧ j = a then 1 else 0) := by
    intro i j
    rw [comm_apply]
    simp only [unitTurn, Matrix.of_apply]
    by_cases h1 : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h1
      simp [ha, hb, hab]
    · by_cases h2 : i = b ∧ j = a
      · obtain ⟨rfl, rfl⟩ := h2
        simp [ha, hb, hab, Ne.symm hab]
      · simp [h1, h2]
  rw [massForm_self_eq]
  simp_rw [hpt]
  simp [Finset.sum_add_distrib, ite_and]
  norm_num

/-- **Every unit kept rotation is massless:** `M_D(E_ab − E_ba) = 0` when `a, b` are on one side. -/
theorem massForm_unit_kept (D : Finset (Fin n)) {a b : Fin n} (h : a ∈ D ↔ b ∈ D) :
    massForm D (unitTurn a b) (unitTurn a b) = 0 := by
  rw [massForm_self_eq]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [comm_apply]
  simp only [unitTurn, Matrix.of_apply]
  by_cases h1 : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h1
    by_cases hi : i ∈ D
    · simp [hi, h.mp hi]
    · simp [hi, mt h.mpr hi]
  · by_cases h2 : i = b ∧ j = a
    · obtain ⟨rfl, rfl⟩ := h2
      by_cases hi : i ∈ D
      · simp [hi, h.mpr hi]
      · simp [hi, mt h.mp hi]
    · simp [h1, h2]

end Comparison

end
