import Comparison.System.Existence.Places
import Comparison.JointCells.Patterns
import Comparison.Article.Splits
import Comparison.Article.Summaries
import Comparison.ArticleStatements.Radar

/-!
# The proof system, the existence layer: the six divisions completed (Propositions 40 to 44, 97)

Book VIII. A line with last-step direction `h` and plane `F = {h, k}` holds six
divisions (Prop. 27): `{}`, `{n}`, `{h, n}`, `{h}`, `F` and `C`, the three lines outside the plane (`sixOf h k`).
Every statement here holds for every last-step direction `h` and every plane `{h, k}`, `h ≠ k`.

* Prop. 40, the table of the six (`prop_40`): type, time-like part, loop signs, phase, kept and moved rotations of the
  fifteen and of the ten, the dimension of the centre (the clock), the mass of every moved unit rotation, and the
  curvature split `F_k = F(A_k) + (A_m ∧ A_m)_k`, `F_m = D_{A_k}A_m` for every connection.
* Prop. 41, the clock of a line (`prop_41`): `iγ_h` and `γ_hγ_k`, with the exponential `e^{iaγ_h}` itself.
* Prop. 42, count and amplitude (`prop_42`), indexed by the divided set `S` of the six.
* Prop. 43, where each piece sits (`prop_43`); Prop. 44, the step at each divided set (`prop_44`); Prop. 97, the
  reflections are radar steps (`prop_97`).
-/

namespace Comparison.System.Existence

open Matrix Complex Kronecker

/-! ## The six divided sets a line holds -/

/-- The three lines outside the plane `{h, k}`, as a divided set of the six. -/
def outside (h k : Fin 5) : Finset (Fin 6) := (({h, k} : Finset (Fin 5))ᶜ).map (Fin.succEmb 5)

/-- The six divided sets a line with last-step direction `h` and plane `{h, k}` holds (Prop. 27): `{}`, `{n}`, `{h, n}`, `{h}`, `F`,
`C`. -/
def sixOf (h k : Fin 5) : List (Finset (Fin 6)) :=
  [∅, {0}, {0, h.succ}, {h.succ}, {h.succ, k.succ}, outside h k]

/-- The type of a division of the six: the size `k` of its smaller part, `k ¦ 6 − k`. -/
def kind (S : Finset (Fin 6)) : ℕ := min S.card (6 - S.card)

/-- The time-like part of a division: its smaller part, on which `θ_S = −1`; none when the parts are equal. -/
def timeLike (S : Finset (Fin 6)) : Finset (Fin 6) :=
  if S.card < 6 - S.card then S else if 6 - S.card < S.card then Sᶜ else ∅

/-- The planes of the six within a side of `S`; their loop `(f_xf_y)²` is `−1` (Prop. 34). -/
def loopsWithin (S : Finset (Fin 6)) : ℕ :=
  (Finset.univ.filter fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ (p.1 ∈ S ↔ p.2 ∈ S)).card

/-- The planes of the six across `S`; their loop is `+1`. -/
def loopsAcross (S : Finset (Fin 6)) : ℕ :=
  (Finset.univ.filter fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ ¬(p.1 ∈ S ↔ p.2 ∈ S)).card

/-- The kept rotations of the fifteen. -/
def keptOf15 (S : Finset (Fin 6)) : ℕ := (Finset.univ.filter (Kept S)).card

/-- The moved rotations of the fifteen. -/
def movedOf15 (S : Finset (Fin 6)) : ℕ := (Finset.univ.filter (Moved S)).card

/-- The kept rotations of the ten that keep the singlet. -/
def keptOf10 (S : Finset (Fin 6)) : ℕ := (Finset.univ.filter fun f : Fin 10 => Kept S (Sum.inr f)).card

/-- The moved rotations of the ten that keep the singlet. -/
def movedOf10 (S : Finset (Fin 6)) : ℕ := (Finset.univ.filter fun f : Fin 10 => Moved S (Sum.inr f)).card

theorem six_table : ∀ h k : Fin 5, h ≠ k →
    (sixOf h k).map kind = [0, 1, 2, 1, 2, 3] ∧
    (sixOf h k).map timeLike = [∅, {0}, {0, h.succ}, {h.succ}, {h.succ, k.succ}, ∅] ∧
    (sixOf h k).map (fun S => (loopsWithin S, loopsAcross S)) =
      [(15, 0), (10, 5), (7, 8), (10, 5), (7, 8), (6, 9)] ∧
    (sixOf h k).map (fun S => (keptOf15 S, movedOf15 S)) =
      [(15, 0), (10, 5), (7, 8), (10, 5), (7, 8), (6, 9)] ∧
    (sixOf h k).map (fun S => (keptOf10 S, movedOf10 S)) =
      [(10, 0), (10, 0), (6, 4), (6, 4), (4, 6), (4, 6)] ∧
    (sixOf h k).map (fun S => if S.card = 2 ∨ S.card = 4 then 1 else 0) = [0, 0, 1, 0, 1, 0] := by
  decide +kernel

theorem six_phases (h k : Fin 5) (hhk : h ≠ k) : (sixOf h k).map zS = [1, I, -1, I, -1, -I] := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := prop_35.2.2.2.2.2.1 h k hhk
  simp only [sixOf, outside, List.map_cons, List.map_nil, e1, e2, e3, e4, e5, e6]

theorem succ_ne_succ {h k : Fin 5} (hhk : h ≠ k) : h.succ ≠ k.succ := fun e => hhk (Fin.succ_injective _ e)

/-- The clock of a line on the six: the unit rotation of the plane of the singlet and the last-step direction. -/
theorem line_clock (h : Fin 5) : IsClock {0, h.succ} (unitTurn 0 h.succ) :=
  ⟨unitTurn_ne_zero (Fin.succ_ne_zero h).symm, Formulas.unitTurn_central_pair (Fin.succ_ne_zero h).symm⟩

/-- The clock of a plane on the six: the unit rotation of the plane of its two lines. -/
theorem plane_clock {h k : Fin 5} (hhk : h ≠ k) : IsClock {h.succ, k.succ} (unitTurn h.succ k.succ) :=
  ⟨unitTurn_ne_zero (succ_ne_succ hhk), Formulas.unitTurn_central_pair (succ_ne_succ hhk)⟩

/-! ## The split of a rotation and of a curvature by a division -/

section Split

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The kept part `X_k = ½(X + θXθ)` of `X` under a division `θ` (`θ² = 1`). -/
noncomputable def keptPart (θ X : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℂ) • (X + θ * X * θ)

/-- The moved part `X_m = ½(X − θXθ)`. -/
noncomputable def movedPart (θ X : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℂ) • (X - θ * X * θ)

theorem theta_theta_mul {θ : Matrix n n ℂ} (hθ : θ * θ = 1) (Y : Matrix n n ℂ) : θ * (θ * Y) = Y := by
  rw [← Matrix.mul_assoc, hθ, Matrix.one_mul]

theorem keptPart_add_movedPart (θ X : Matrix n n ℂ) : keptPart θ X + movedPart θ X = X := by
  unfold keptPart movedPart
  rw [← smul_add, show X + θ * X * θ + (X - θ * X * θ) = (2 : ℂ) • X by rw [two_smul]; abel, smul_smul]
  norm_num

theorem keptPart_isKept {θ : Matrix n n ℂ} (hθ : θ * θ = 1) (X : Matrix n n ℂ) :
    Article.IsKept θ (keptPart θ X) := by
  unfold Article.IsKept keptPart
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hθ,
    theta_theta_mul hθ, Matrix.mul_one]
  congr 1
  abel

theorem movedPart_isMoved {θ : Matrix n n ℂ} (hθ : θ * θ = 1) (X : Matrix n n ℂ) :
    Article.IsMoved θ (movedPart θ X) := by
  unfold Article.IsMoved movedPart
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hθ,
    theta_theta_mul hθ, Matrix.mul_one]
  rw [← smul_neg]
  congr 1
  abel

theorem keptPart_add (θ X Y : Matrix n n ℂ) : keptPart θ (X + Y) = keptPart θ X + keptPart θ Y := by
  unfold keptPart
  rw [Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

theorem keptPart_sub (θ X Y : Matrix n n ℂ) : keptPart θ (X - Y) = keptPart θ X - keptPart θ Y := by
  unfold keptPart
  rw [Matrix.mul_sub, Matrix.sub_mul, ← smul_sub]
  congr 1
  abel

theorem movedPart_add (θ X Y : Matrix n n ℂ) : movedPart θ (X + Y) = movedPart θ X + movedPart θ Y := by
  unfold movedPart
  rw [Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

theorem movedPart_sub (θ X Y : Matrix n n ℂ) : movedPart θ (X - Y) = movedPart θ X - movedPart θ Y := by
  unfold movedPart
  rw [Matrix.mul_sub, Matrix.sub_mul, ← smul_sub]
  congr 1
  abel

theorem keptPart_of_kept {θ : Matrix n n ℂ} (hθ : θ * θ = 1) {K : Matrix n n ℂ} (hK : Article.IsKept θ K) :
    keptPart θ K = K := by
  have hK' : K * θ = θ * K := hK
  unfold keptPart
  rw [Matrix.mul_assoc, hK', theta_theta_mul hθ, ← two_smul ℂ K, smul_smul]
  norm_num

theorem keptPart_of_moved {θ : Matrix n n ℂ} (hθ : θ * θ = 1) {M : Matrix n n ℂ} (hM : Article.IsMoved θ M) :
    keptPart θ M = 0 := by
  have hM' : M * θ = -(θ * M) := hM
  unfold keptPart
  rw [Matrix.mul_assoc, hM', Matrix.mul_neg, theta_theta_mul hθ, add_neg_cancel, smul_zero]

theorem movedPart_of_kept {θ : Matrix n n ℂ} (hθ : θ * θ = 1) {K : Matrix n n ℂ} (hK : Article.IsKept θ K) :
    movedPart θ K = 0 := by
  have hK' : K * θ = θ * K := hK
  unfold movedPart
  rw [Matrix.mul_assoc, hK', theta_theta_mul hθ, sub_self, smul_zero]

theorem movedPart_of_moved {θ : Matrix n n ℂ} (hθ : θ * θ = 1) {M : Matrix n n ℂ} (hM : Article.IsMoved θ M) :
    movedPart θ M = M := by
  have hM' : M * θ = -(θ * M) := hM
  unfold movedPart
  rw [Matrix.mul_assoc, hM', Matrix.mul_neg, theta_theta_mul hθ, sub_neg_eq_add, ← two_smul ℂ M, smul_smul]
  norm_num

/-- **The split is unique:** a kept `K` and a moved `M` with `X = K + M` are the kept and the moved parts. -/
theorem split_unique {θ : Matrix n n ℂ} (hθ : θ * θ = 1) {X K M : Matrix n n ℂ} (hK : Article.IsKept θ K)
    (hM : Article.IsMoved θ M) (hX : X = K + M) : K = keptPart θ X ∧ M = movedPart θ X := by
  subst hX
  rw [keptPart_add, movedPart_add, keptPart_of_kept hθ hK, keptPart_of_moved hθ hM, movedPart_of_kept hθ hK,
    movedPart_of_moved hθ hM]
  simp

/-- The curvature at a point, from the values `A_μ` of a connection and its derivatives `∂_μA_ν` there:
`F_μν = ∂_μA_ν − ∂_νA_μ + [A_μ, A_ν]`. -/
def curvAt {d : ℕ} (A : Fin d → Matrix n n ℂ) (dA : Fin d → Fin d → Matrix n n ℂ) (μ ν : Fin d) :
    Matrix n n ℂ :=
  dA μ ν - dA ν μ + Article.brk (A μ) (A ν)

/-- The covariant derivative of `B` along `A` at a point: `(D_A B)_μν = ∂_μB_ν − ∂_νB_μ + [A_μ, B_ν] + [B_μ, A_ν]`. -/
def covDAt {d : ℕ} (A B : Fin d → Matrix n n ℂ) (dB : Fin d → Fin d → Matrix n n ℂ) (μ ν : Fin d) :
    Matrix n n ℂ :=
  dB μ ν - dB ν μ + Article.brk (A μ) (B ν) + Article.brk (B μ) (A ν)

/-- **The curvature splits by the division.** For every connection `A` (its values and derivatives at a point) and
every division `θ` (`θ² = 1`), with `A_k`, `A_m` the kept and the moved parts (whose derivatives are the kept and the
moved parts of the derivatives, `keptPart_hasFDerivAt`): `F = F_k + F_m`, `F_k` kept, `F_m` moved,
`F_k = F(A_k) + [A_m, A_m]` with `[A_m, A_m]` kept, and `F_m = D_{A_k}A_m`. -/
theorem curvature_split_parts {d : ℕ} {θ : Matrix n n ℂ} (hθ : θ * θ = 1) (A : Fin d → Matrix n n ℂ)
    (dA : Fin d → Fin d → Matrix n n ℂ) (μ ν : Fin d) :
    curvAt A dA μ ν = keptPart θ (curvAt A dA μ ν) + movedPart θ (curvAt A dA μ ν) ∧
    Article.IsKept θ (keptPart θ (curvAt A dA μ ν)) ∧ Article.IsMoved θ (movedPart θ (curvAt A dA μ ν)) ∧
    keptPart θ (curvAt A dA μ ν) =
      curvAt (fun μ => keptPart θ (A μ)) (fun μ ν => keptPart θ (dA μ ν)) μ ν +
        Article.brk (movedPart θ (A μ)) (movedPart θ (A ν)) ∧
    Article.IsKept θ (Article.brk (movedPart θ (A μ)) (movedPart θ (A ν))) ∧
    movedPart θ (curvAt A dA μ ν) =
      covDAt (fun μ => keptPart θ (A μ)) (fun μ => movedPart θ (A μ)) (fun μ ν => movedPart θ (dA μ ν)) μ ν := by
  have hk : ∀ μ, Article.IsKept θ (keptPart θ (A μ)) := fun μ => keptPart_isKept hθ (A μ)
  have hm : ∀ μ, Article.IsMoved θ (movedPart θ (A μ)) := fun μ => movedPart_isMoved hθ (A μ)
  have hMM : Article.IsKept θ (Article.brk (movedPart θ (A μ)) (movedPart θ (A ν))) :=
    Article.kept_sub (Article.moved_mul_moved (hm μ) (hm ν)) (Article.moved_mul_moved (hm ν) (hm μ))
  have hKK : Article.IsKept θ (Article.brk (keptPart θ (A μ)) (keptPart θ (A ν))) :=
    Article.kept_sub (Article.kept_mul_kept (hk μ) (hk ν)) (Article.kept_mul_kept (hk ν) (hk μ))
  have hKM : Article.IsMoved θ (Article.brk (keptPart θ (A μ)) (movedPart θ (A ν))) :=
    Article.moved_sub (Article.kept_mul_moved (hk μ) (hm ν)) (Article.moved_mul_kept (hm ν) (hk μ))
  have hMK : Article.IsMoved θ (Article.brk (movedPart θ (A μ)) (keptPart θ (A ν))) :=
    Article.moved_sub (Article.moved_mul_kept (hm μ) (hk ν)) (Article.kept_mul_moved (hk ν) (hm μ))
  have hbrk : Article.brk (A μ) (A ν) =
      Article.brk (keptPart θ (A μ)) (keptPart θ (A ν)) + Article.brk (movedPart θ (A μ)) (movedPart θ (A ν)) +
        (Article.brk (keptPart θ (A μ)) (movedPart θ (A ν)) +
          Article.brk (movedPart θ (A μ)) (keptPart θ (A ν))) := by
    have e1 := keptPart_add_movedPart θ (A μ)
    have e2 := keptPart_add_movedPart θ (A ν)
    calc Article.brk (A μ) (A ν)
        = Article.brk (keptPart θ (A μ) + movedPart θ (A μ)) (keptPart θ (A ν) + movedPart θ (A ν)) := by
          rw [e1, e2]
      _ = _ := by
          simp only [Article.brk]
          noncomm_ring
  refine ⟨(keptPart_add_movedPart θ _).symm, keptPart_isKept hθ _, movedPart_isMoved hθ _, ?_, hMM, ?_⟩
  · simp only [curvAt]
    rw [hbrk]
    simp only [keptPart_add, keptPart_sub, keptPart_of_kept hθ hKK, keptPart_of_kept hθ hMM,
      keptPart_of_moved hθ hKM, keptPart_of_moved hθ hMK, add_zero]
    abel
  · simp only [curvAt, covDAt]
    rw [hbrk]
    simp only [movedPart_add, movedPart_sub, movedPart_of_kept hθ hKK, movedPart_of_kept hθ hMM,
      movedPart_of_moved hθ hKM, movedPart_of_moved hθ hMK, zero_add]
    abel

/-- `X ↦ X_k` as a real-linear map. -/
noncomputable def keptLin (θ : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ where
  toFun := keptPart θ
  map_add' X Y := keptPart_add θ X Y
  map_smul' c X := by
    simp only [keptPart, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
    exact smul_comm _ _ _

/-- `X ↦ X_m` as a real-linear map. -/
noncomputable def movedLin (θ : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ where
  toFun := movedPart θ
  map_add' X Y := movedPart_add θ X Y
  map_smul' c X := by
    simp only [movedPart, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
    exact smul_comm _ _ _

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- **The derivative of the kept part is the kept part of the derivative.** -/
theorem keptPart_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (θ : Matrix n n ℂ)
    {f : E → Matrix n n ℂ} {f' : E →L[ℝ] Matrix n n ℂ} {x : E} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => keptPart θ (f y)) ((LinearMap.toContinuousLinearMap (keptLin θ)).comp f') x :=
  (LinearMap.toContinuousLinearMap (keptLin θ)).hasFDerivAt.comp x hf

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- **The derivative of the moved part is the moved part of the derivative.** -/
theorem movedPart_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (θ : Matrix n n ℂ)
    {f : E → Matrix n n ℂ} {f' : E →L[ℝ] Matrix n n ℂ} {x : E} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => movedPart θ (f y)) ((LinearMap.toContinuousLinearMap (movedLin θ)).comp f') x :=
  (LinearMap.toContinuousLinearMap (movedLin θ)).hasFDerivAt.comp x hf

end Split

theorem theta_mul_self (S : Finset (Fin 6)) : theta ℂ S * theta ℂ S = 1 := by
  rw [theta, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext c
  split_ifs <;> norm_num

/-! ## Proposition 40 -/

/-- **Proposition 40 (the table of the six).** For every last-step direction `h` and plane `{h, k}`, the six divisions a line holds,
`{}`, `{n}`, `{h, n}`, `{h}`, `F = {h, k}`, `C`, have: the types `0¦6, 1¦5, 2¦4, 1¦5, 2¦4, 3¦3`; the time-like
part (the smaller part, where `θ_S = −1`): none, the singlet, the singlet and `h`, the last-step direction, the plane, none; the loops
`−1/+1`: `15/0, 10/5, 7/8, 10/5, 7/8, 6/9` (a loop `(f_xf_y)²` is `−1` within a side, `+1` across); the phases
`z_S = 1, i, −1, i, −1, −i`; kept/moved of the fifteen `15/0, 10/5, 7/8, 10/5, 7/8, 6/9` and of the ten
`10/0, 10/0, 6/4, 6/4, 4/6, 4/6`; a centre of the kept rotations of dimension `0, 0, 1, 0, 1, 0`, the clocks
`E_{n h} − E_{h n}` at `{h, n}` and `E_{h k} − E_{k h}` at `F` (the rotations of `iγ_h` and `γ_hγ_k`, Prop. 41); every
moved unit rotation has `M_S = 2`; and for every connection the curvature splits as `A = A_k + A_m`,
`F_k = F(A_k) + (A_m ∧ A_m)_k`, `F_m = D_{A_k}A_m` (the derivatives of the parts are the parts of the derivative,
`keptPart_hasFDerivAt`, `movedPart_hasFDerivAt`).

The real forms `SU(4)`, `SU*(4)`, `SU(2,2)`, `SL(4, ℝ)` and the balanced directions `S⁴`, `(S¹ × S³)/ℤ₂`,
`(S² × S²)/ℤ₂` of Table IV are Prop. 21's at the type.

Recognition: `{}` the universality of gravity; `{n}` the sign of time of every pair and the sphere of lines; `{h}`
the ten rotations split at the last-step direction, `6 + 4`, spin connection and co-frame; `{h, n}` the line's own clock; `F` the common
time and light; `C` two times and no clock, colour. Uses Props. 21, 22, 27, 34, 35, 39, Definition 28. -/
theorem prop_40 (h k : Fin 5) (hhk : h ≠ k) :
    (sixOf h k).map kind = [0, 1, 2, 1, 2, 3] ∧
    (sixOf h k).map timeLike = [∅, {0}, {0, h.succ}, {h.succ}, {h.succ, k.succ}, ∅] ∧
    (∀ (S : Finset (Fin 6)) (c : Fin 6), thetaAt S c = -1 ↔ c ∈ S) ∧
    (sixOf h k).map (fun S => (loopsWithin S, loopsAcross S)) =
      [(15, 0), (10, 5), (7, 8), (10, 5), (7, 8), (6, 9)] ∧
    (∀ (S : Finset (Fin 6)) (x y : Fin 6), x ≠ y →
      (SysExt.halfStep S x * SysExt.halfStep S y) * (SysExt.halfStep S x * SysExt.halfStep S y) =
        (if (x ∈ S ↔ y ∈ S) then (-1 : ℂ) else 1) • 1) ∧
    (sixOf h k).map zS = [1, I, -1, I, -1, -I] ∧
    (sixOf h k).map (fun S => (keptOf15 S, movedOf15 S)) =
      [(15, 0), (10, 5), (7, 8), (10, 5), (7, 8), (6, 9)] ∧
    (sixOf h k).map (fun S => (keptOf10 S, movedOf10 S)) =
      [(10, 0), (10, 0), (6, 4), (6, 4), (4, 6), (4, 6)] ∧
    (sixOf h k).map (fun S => Module.finrank ℝ (centreSub S)) = [0, 0, 1, 0, 1, 0] ∧
    IsClock {0, h.succ} (unitTurn 0 h.succ) ∧ IsClock {h.succ, k.succ} (unitTurn h.succ k.succ) ∧
    (∀ S ∈ sixOf h k, ∀ a b : Fin 6, a ∈ S → b ∉ S → massForm S (unitTurn a b) (unitTurn a b) = 2) ∧
    (∀ S ∈ sixOf h k, ∀ (d : ℕ) (A : Fin d → Matrix (Fin 6) (Fin 6) ℂ)
        (dA : Fin d → Fin d → Matrix (Fin 6) (Fin 6) ℂ) (μ ν : Fin d),
      curvAt A dA μ ν = keptPart (theta ℂ S) (curvAt A dA μ ν) + movedPart (theta ℂ S) (curvAt A dA μ ν) ∧
      Article.IsKept (theta ℂ S) (keptPart (theta ℂ S) (curvAt A dA μ ν)) ∧
      Article.IsMoved (theta ℂ S) (movedPart (theta ℂ S) (curvAt A dA μ ν)) ∧
      keptPart (theta ℂ S) (curvAt A dA μ ν) =
        curvAt (fun μ => keptPart (theta ℂ S) (A μ)) (fun μ ν => keptPart (theta ℂ S) (dA μ ν)) μ ν +
          Article.brk (movedPart (theta ℂ S) (A μ)) (movedPart (theta ℂ S) (A ν)) ∧
      Article.IsKept (theta ℂ S) (Article.brk (movedPart (theta ℂ S) (A μ)) (movedPart (theta ℂ S) (A ν))) ∧
      movedPart (theta ℂ S) (curvAt A dA μ ν) =
        covDAt (fun μ => keptPart (theta ℂ S) (A μ)) (fun μ => movedPart (theta ℂ S) (A μ))
          (fun μ ν => movedPart (theta ℂ S) (dA μ ν)) μ ν) := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := six_table h k hhk
  refine ⟨t1, t2, fun S c => ?_, t3, fun S x y hxy => ?_, six_phases h k hhk, t4, t5, ?_, line_clock h,
    plane_clock hhk, fun S _ a b ha hb => massForm_unit_moved S ha hb,
    fun S _ d A dA μ ν => curvature_split_parts (theta_mul_self S) A dA μ ν⟩
  · by_cases hc : c ∈ S
    · simp [thetaAt, hc]
    · simp only [thetaAt, hc, if_false, iff_false]
      norm_num
  · rw [SysExt.half_loop_sq S hxy]
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx, hy]
  · have hfr : (fun S => Module.finrank ℝ (centreSub S)) =
        fun S : Finset (Fin 6) => if S.card = 2 ∨ S.card = 4 then 1 else 0 :=
      funext finrank_centreSub
    rw [hfr]
    exact t6

/-! ## Proposition 41 -/

set_option backward.isDefEq.respectTransparency false in
/-- `e^{θM} = cos θ + sin θ M` for a complex matrix with `M² = −1`, `θ` real. -/
theorem cmatrix_exp_smul_of_sq_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (hM : M * M = -1) (θ : ℝ) :
    NormedSpace.exp (θ • M) = Real.cos θ • (1 : Matrix ι ι ℂ) + Real.sin θ • M :=
  open scoped Matrix.Norms.Operator in exp_smul_of_sq_neg M hM θ

theorem iγ_sq (h : Fin 5) : (I • γ h) * (I • γ h) = -1 := by
  rw [smul_mul_smul_comm, γ_mul_self, I_mul_I, neg_one_smul]

/-- **The exponential of the clock:** `e^{a·iγ_h} = cos a + i sin a γ_h`. -/
theorem exp_iγ (a : ℝ) (h : Fin 5) : NormedSpace.exp (a • (I • γ h)) = expIγ a h := by
  rw [cmatrix_exp_smul_of_sq_neg _ (iγ_sq h), expIγ]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem plane_of_pair : ∀ h k : Fin 5, h ≠ k → ∃ f : Fin 10,
    (Comparison.planeLines f = (h, k) ∨ Comparison.planeLines f = (k, h)) ∧ Kept {h.succ, k.succ} (Sum.inr f) ∧
      Moved {h.succ} (Sum.inr f) ∧ Moved {k.succ} (Sum.inr f) := by
  decide +kernel

/-- **Proposition 41 (the clock of a line, and its mass).** `iγ_h` is the clock of `{h, n}`: it is kept, it
commutes with every rotation `{h, n}` keeps, it turns the plane `(n, h)` of the six (as `−2(E_{n h} − E_{h n})`), whose
unit rotation is a clock and spans the centre of the kept rotations; at `{h}` it is moved;
`e^{iaγ_h} = cos a + i sin a γ_h`, `(e^{iaγ_h} ⊗ e^{iaγ_h})Ω = cos 2a Ω + sin 2a iℓ_h`, `e^{i(π/2)γ_h} = iγ_h`;
`γ_hγ_k` (the plane's rotation, `±γ_hγ_k`) is the clock of `F = {h, k}`: kept, commuting with every rotation `F` keeps, its
unit rotation spans the centre; and it is moved at `{h}` and at `{k}`.

Recognition: the line's own time and its rest mass are one rotation, de Broglie's internal clock, `E = mc²`; the plane's
clock is the common time, the conformal time translation of `SU(2,2)`. Uses Props. 17, 21, 40, Definition 28. -/
theorem prop_41 (h k : Fin 5) (hhk : h ≠ k) :
    gen (Sum.inl h) = I • γ h ∧ plane (Sum.inl h) = (0, h.succ) ∧
    Kept {0, h.succ} (Sum.inl h) ∧
    (∀ x, Kept {0, h.succ} x → gen (Sum.inl h) * gen x = gen x * gen (Sum.inl h)) ∧
    Moved {h.succ} (Sum.inl h) ∧
    (∀ c : Fin 6, act (gen (Sum.inl h)) (sixP1 c) = ∑ d, ((rotMat (0, h.succ) d c : ℤ) : ℂ) • sixP1 d) ∧
    (rotMat (0, h.succ)).map (Int.cast : ℤ → ℝ) = (-2 : ℝ) • unitTurn 0 h.succ ∧
    IsClock {0, h.succ} (unitTurn 0 h.succ) ∧
    centreSub {0, h.succ} = Submodule.span ℝ {unitTurn 0 h.succ} ∧
    (∀ a : ℝ, NormedSpace.exp (a • (I • γ h)) = (Real.cos a : ℂ) • 1 + (I * Real.sin a) • γ h) ∧
    (∀ a : ℝ, (NormedSpace.exp (a • (I • γ h)) ⊗ₖ NormedSpace.exp (a • (I • γ h))) *ᵥ Ω =
      (Real.cos (2 * a) : ℂ) • Ω + (Real.sin (2 * a) : ℂ) • (I • ell h)) ∧
    NormedSpace.exp ((Real.pi / 2) • (I • γ h)) = I • γ h ∧
    (∃ f : Fin 10, (Comparison.planeLines f = (h, k) ∨ Comparison.planeLines f = (k, h)) ∧
      (gen (Sum.inr f) = -(γ h * γ k) ∨ gen (Sum.inr f) = γ h * γ k) ∧
      Kept {h.succ, k.succ} (Sum.inr f) ∧
      (∀ x, Kept {h.succ, k.succ} x → gen (Sum.inr f) * gen x = gen x * gen (Sum.inr f)) ∧
      Moved {h.succ} (Sum.inr f) ∧ Moved {k.succ} (Sum.inr f)) ∧
    IsClock {h.succ, k.succ} (unitTurn h.succ k.succ) ∧
    centreSub {h.succ, k.succ} = Submodule.span ℝ {unitTurn h.succ k.succ} := by
  have h0 : (0 : Fin 6) ≠ h.succ := (Fin.succ_ne_zero h).symm
  refine ⟨gen_inl h, rfl, clock_line_kept h, clock_line_central h, clock_line_moved h,
    fun c => gen_acts_matrix (Sum.inl h) c, rotMat_eq (0, h.succ) h0, line_clock h, centreSub_pair h0,
    fun a => exp_iγ a h, fun a => ?_, ?_, ?_, plane_clock hhk, centreSub_pair (succ_ne_succ hhk)⟩
  · rw [exp_iγ]
    exact clock_turns_singlet a h
  · rw [exp_iγ, quarter_turn]
  · obtain ⟨f, hf, hkept, hm1, hm2⟩ := plane_of_pair h k hhk
    have hset : ({h.succ, k.succ} : Finset (Fin 6)) =
        {(Comparison.planeLines f).1.succ, (Comparison.planeLines f).2.succ} := by
      rcases hf with hf | hf
      · rw [hf]
      · rw [hf, Finset.pair_comm]
    refine ⟨f, hf, ?_, hkept, fun x hx => clock_plane_central f x (hset ▸ hx), hm1, hm2⟩
    rw [gen_inr]
    rcases hf with hf | hf
    · left
      rw [hf]
    · right
      rw [hf]
      dsimp only
      rw [γ_anticomm (Ne.symm hhk), neg_neg]

/-! ## Proposition 42 -/

/-- The lines a division of the six divides when the singlet is undivided: the lines in `S` if `n ∉ S`, the lines
outside `S` otherwise. -/
def divLines (S : Finset (Fin 6)) : Finset (Fin 5) :=
  if (0 : Fin 6) ∈ S then Finset.univ.filter (fun t => t.succ ∉ S) else Finset.univ.filter (fun t => t.succ ∈ S)

theorem divLines_parity : ∀ S : Finset (Fin 6), (divLines S).card % 2 = S.card % 2 := by
  decide +kernel

theorem divOf_divLines : ∀ S : Finset (Fin 6),
    JointCells.Patterns.divOf (divLines S) = if (0 : Fin 6) ∈ S then Sᶜ else S := by
  decide +kernel

theorem kept_iff_divLines (S : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) :
    Kept S x ↔ Kept (JointCells.Patterns.divOf (divLines S)) x := by
  rw [divOf_divLines]
  split_ifs
  · exact (kept_compl S x).symm
  · exact Iff.rfl

theorem gammaDZ_J_unitary : ∀ D : Finset (Fin 5), (gammaDZ D * JZ)ᴴ * (gammaDZ D * JZ) = 1 := by
  decide +kernel

theorem gammaD_J_unitary (D : Finset (Fin 5)) :
    (gammaD D * Comparison.J)ᴴ * (gammaD D * Comparison.J) = 1 := by
  have hsemi : Function.Semiconj GaussianInt.toComplex star star := by
    intro a
    rw [GaussianInt.toComplex_star]
    rfl
  have h := congrArg (fun M => Matrix.map M GaussianInt.toComplex) (gammaDZ_J_unitary D)
  simp only [Matrix.map_mul, Matrix.conjTranspose_map _ hsemi, gammaDZ_map, JZ_map] at h
  rw [h, Matrix.map_one _ (map_zero _) (map_one _)]

/-- `C_D = γ_D Θ`. -/
theorem Cop_eq (D : Finset (Fin 5)) (v : Four → ℂ) : Cop D v = gammaD D *ᵥ Θ v := by
  rw [Cop, Θ, Matrix.mulVec_mulVec]

/-- `C_D` keeps lengths and conjugates: `⟨C_D v, C_D u⟩ = ⟨u, v⟩`. -/
theorem Cop_inner (D : Finset (Fin 5)) (u v : Four → ℂ) : star (Cop D v) ⬝ᵥ Cop D u = star u ⬝ᵥ v := by
  have hU := gammaD_J_unitary D
  rw [Cop, Cop, Matrix.star_mulVec, star_star, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU,
    Matrix.one_mulVec, dotProduct_comm]

theorem amplitude_smul_left (D : Finset (Fin 5)) (c : ℂ) (v w : Four → ℂ) :
    star (Cop D (c • v)) ⬝ᵥ w = c * (star (Cop D v) ⬝ᵥ w) := by
  rw [Cop, Cop, star_smul, Matrix.mulVec_smul, star_smul, star_star, smul_dotProduct, smul_eq_mul]

theorem amplitude_add_left (D : Finset (Fin 5)) (v v' w : Four → ℂ) :
    star (Cop D (v + v')) ⬝ᵥ w = star (Cop D v) ⬝ᵥ w + star (Cop D v') ⬝ᵥ w := by
  rw [Cop, Cop, Cop, star_add, Matrix.mulVec_add, star_add, add_dotProduct]

theorem amplitude_smul_right (D : Finset (Fin 5)) (c : ℂ) (v w : Four → ℂ) :
    star (Cop D v) ⬝ᵥ (c • w) = c * (star (Cop D v) ⬝ᵥ w) := by
  rw [dotProduct_smul, smul_eq_mul]

theorem amplitude_add_right (D : Finset (Fin 5)) (v w w' : Four → ℂ) :
    star (Cop D v) ⬝ᵥ (w + w') = star (Cop D v) ⬝ᵥ w + star (Cop D v) ⬝ᵥ w' := by
  rw [dotProduct_add]

theorem countSign_odd : ∀ S : Finset (Fin 6), Odd S.card →
    (countSign (divLines S).card = -1 ↔ ((divLines S).card = 1 ∨ (divLines S).card = 5)) ∧
    (countSign (divLines S).card = 1 ↔ (divLines S).card = 3) := by
  decide +kernel

theorem twin_parity : ∀ S : Finset (Fin 6), (twin S).card % 2 ≠ S.card % 2 := by
  decide +kernel

/-- **Proposition 42 (count and amplitude).** For every divided set `S` of the six, read with the singlet undivided as the
division of the lines `D = divLines S` (`|D| ≡ |S|` mod 2): the rotations `S` keeps are exactly those that commute with
`γ_D` (`|S|` even) or with the antilinear `C_S = γ_DΘ` (`|S|` odd); for `S` even the kept form
`h_S = i^{r(r−1)/2}γ_D` is Hermitian and `⟨v, h_S v⟩` is real, a count; for `S` odd, `⟨C_S v, w⟩` is linear in `v`
and in `w`, an amplitude, `C_S² = s_r`, `⟨C_S v, w⟩ = s_r ⟨C_S w, v⟩` (antisymmetric where `C² = −1`, `r = 1, 5`;
symmetric where `C² = +1`, `r = 3`), and `⟨C_S v, C_S u⟩ = ⟨u, v⟩`, so `|⟨C_S v, w⟩|²` is a chance between two
states; `z_S = det q_S`, `z_S² = det θ_S`, `+1` for `S` even and `−1` for `S` odd; and a counterpart has the other parity.

Recognition: a count is a probability, an amplitude a transition amplitude; matter is counted, its counterpart with `n` added is a
quantum amplitude. Uses Props. 7, 19, 35, the Lemma of the divisions (the section on divisions), Definition 29. -/
theorem prop_42 :
    (∀ S : Finset (Fin 6), (divLines S).card % 2 = S.card % 2) ∧
    (∀ (S : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10), Kept S x ↔
      (if (divLines S).card % 2 = 0 then gen x * gammaD (divLines S) = gammaD (divLines S) * gen x
       else gen x * (gammaD (divLines S) * Comparison.J) =
         (gammaD (divLines S) * Comparison.J) * (gen x).map star)) ∧
    (∀ S : Finset (Fin 6), Even S.card →
      (hermForm (divLines S))ᴴ = hermForm (divLines S) ∧
      ∀ v : Four → ℂ, (star v ⬝ᵥ (hermForm (divLines S) *ᵥ v)).im = 0) ∧
    (∀ S : Finset (Fin 6), Odd S.card →
      (∀ v : Four → ℂ, Cop (divLines S) v = gammaD (divLines S) *ᵥ Θ v) ∧
      (∀ (c : ℂ) (v w : Four → ℂ), star (Cop (divLines S) (c • v)) ⬝ᵥ w = c * (star (Cop (divLines S) v) ⬝ᵥ w)) ∧
      (∀ v v' w : Four → ℂ, star (Cop (divLines S) (v + v')) ⬝ᵥ w =
        star (Cop (divLines S) v) ⬝ᵥ w + star (Cop (divLines S) v') ⬝ᵥ w) ∧
      (∀ (c : ℂ) (v w : Four → ℂ), star (Cop (divLines S) v) ⬝ᵥ (c • w) = c * (star (Cop (divLines S) v) ⬝ᵥ w)) ∧
      (∀ v w w' : Four → ℂ, star (Cop (divLines S) v) ⬝ᵥ (w + w') =
        star (Cop (divLines S) v) ⬝ᵥ w + star (Cop (divLines S) v) ⬝ᵥ w') ∧
      (∀ v : Four → ℂ, Cop (divLines S) (Cop (divLines S) v) = (countSign (divLines S).card : ℂ) • v) ∧
      (∀ v w : Four → ℂ, star (Cop (divLines S) v) ⬝ᵥ w =
        (countSign (divLines S).card : ℂ) * (star (Cop (divLines S) w) ⬝ᵥ v)) ∧
      (countSign (divLines S).card = -1 ↔ ((divLines S).card = 1 ∨ (divLines S).card = 5)) ∧
      (countSign (divLines S).card = 1 ↔ (divLines S).card = 3) ∧
      (∀ u v : Four → ℂ, star (Cop (divLines S) v) ⬝ᵥ Cop (divLines S) u = star u ⬝ᵥ v)) ∧
    (∀ S : Finset (Fin 6), zS S = (half S).det ∧ zS S ^ 2 = (theta ℂ S).det ∧
      (Even S.card → (theta ℂ S).det = 1) ∧ (Odd S.card → (theta ℂ S).det = -1)) ∧
    (∀ S : Finset (Fin 6), (twin S).card % 2 ≠ S.card % 2) := by
  refine ⟨divLines_parity, fun S x => (kept_iff_divLines S x).trans (JointCells.Patterns.kept_iff_form _ x),
    fun S hS => ?_, fun S hS => ?_, fun S => ?_, twin_parity⟩
  · have hD : (divLines S).card % 2 = 0 := by
      rw [divLines_parity]
      exact Nat.even_iff.mp hS
    have hH := hermForm_hermitian (divLines S) hD
    refine ⟨hH, fun v => ?_⟩
    have h1 := Matrix.IsHermitian.star_dotProduct_mulVec_comm hH v v
    have h2 := congrArg Complex.im h1
    rw [Complex.star_def, Complex.conj_im] at h2
    linarith
  · obtain ⟨c1, c2⟩ := countSign_odd S hS
    exact ⟨Cop_eq _, amplitude_smul_left _, amplitude_add_left _, amplitude_smul_right _,
      amplitude_add_right _, C_sq _, amplitude_symm _, c1, c2, Cop_inner _⟩
  · obtain ⟨z1, z2⟩ := prop_35.2.2.2.2.1 S
    refine ⟨(det_half S).symm, z1, fun he => ?_, fun ho => ?_⟩
    · rw [z2, he.neg_one_pow]
    · rw [z2, ho.neg_one_pow]

/-! ## Proposition 43 -/

/-- **Proposition 43 (where each piece sits).** An excursion closes the two-spinor state of a line to itself, the singlet, whose
divided set is `{}`, with the counterpart `{n}`; a step along `t` makes `ℓ_t`, divided set `{t, n}`, counterpart `{t}`; for every last-step direction `h`
and plane `{h, k}` of a line (Prop. 27: `r_{k,k} = Ω`, `r_{k,k−1} = ℓ_h`, `r_{k,k−2} = ±e_{hk}`), the three two-spinor states
have the divided sets `{}`, `{h, n}`, `{h, k}` and the counterparts `{n}`, `{h}`, `C` (the three lines outside the plane); every
symmetric state `e_{ab}` has the divided set `{a, b}` and the counterpart `{a, b}'`, the three lines outside it; every divided set is
even (a count, Prop. 42) and its counterpart with `n` added odd (an amplitude).

Recognition: `{}` carries gravity, the proton and the cosmos; `{n}` sizes and moments; `{t, n}` the step; `{t}`
colour per vertex and `α_s`; `{h, n}` the clock and the weak contact; `{h}` the Higgs; `F` the electric plane and
light; `C` the strong force; `{a, b}` the leptons and `{a, b}'` the quarks. Uses Props. 27, 42, Definition 29. -/
theorem prop_43 :
    (dividedSet 0 = ∅ ∧ twin ∅ = {0}) ∧
    (∀ t : Fin 5, dividedSet (transition t 0) = {0, t.succ} ∧ twin {0, t.succ} = {t.succ}) ∧
    (∀ h k : Fin 5, h ≠ k →
      dividedSet (relOfWord []) = ∅ ∧ dividedSet (relOfWord [h]) = {0, h.succ} ∧ twin {0, h.succ} = {h.succ} ∧
      dividedSet (relOfWord [h, k]) = {h.succ, k.succ} ∧ twin {h.succ, k.succ} = outside h k) ∧
    (∀ a b : Fin 5, a ≠ b → ∀ r : Fin 16, disagreeSet r = {a, b} →
      dividedSet r = {a.succ, b.succ} ∧ twin {a.succ, b.succ} = outside a b) ∧
    (∀ r : Fin 16, Even (dividedSet r).card ∧ Odd (twin (dividedSet r)).card) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## Proposition 44 -/

/-- The half of a divided set on the five directions: `i` on the lines in `S`, `1` on the others. -/
noncomputable def halfLines (S : Finset (Fin 6)) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal fun t => if t.succ ∈ S then I else 1

/-- The square a divided set takes of its half on the five directions: the Hermitian square `q†q` at an even divided set (a
count), the bilinear square `qᵀq` at an odd one (an amplitude). -/
noncomputable def GS (S : Finset (Fin 6)) : Matrix (Fin 5) (Fin 5) ℂ :=
  if Even S.card then (halfLines S)ᴴ * halfLines S else (halfLines S)ᵀ * halfLines S

theorem halfLines_herm (S : Finset (Fin 6)) : (halfLines S)ᴴ * halfLines S = 1 := by
  rw [halfLines, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext t
  simp only [Pi.star_apply]
  split_ifs <;> simp [Complex.star_def]

theorem halfLines_bil (S : Finset (Fin 6)) :
    (halfLines S)ᵀ * halfLines S = Matrix.diagonal fun t => if t.succ ∈ S then -1 else 1 := by
  rw [halfLines, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext t
  split_ifs <;> simp

theorem GS_even {S : Finset (Fin 6)} (he : Even S.card) : GS S = 1 := by
  rw [GS, if_pos he, halfLines_herm]

theorem GS_odd {S : Finset (Fin 6)} (ho : Odd S.card) :
    GS S = Matrix.diagonal fun t => if t.succ ∈ S then -1 else 1 := by
  rw [GS, if_neg (Nat.not_even_iff_odd.mpr ho), halfLines_bil]

theorem GS_eq (S : Finset (Fin 6)) : GS S = dividedSetG (Law.linesOf S) (decide (Odd S.card)) := by
  by_cases he : Even S.card
  · have ho : ¬Odd S.card := Nat.not_odd_iff_even.mpr he
    rw [GS_even he, dividedSetG, ← Matrix.diagonal_one]
    congr 1
    funext t
    simp [ho]
  · have ho : Odd S.card := Nat.not_even_iff_odd.mp he
    rw [GS_odd ho, dividedSetG]
    congr 1
    funext t
    simp [ho, Law.linesOf]

/-- `L_S = 𝟏ᵀG_S𝟏`. -/
theorem sum_GS (S : Finset (Fin 6)) : ∑ i, ∑ j, GS S i j = Law.LS S := by
  rw [GS_eq, dividedSetL, Law.card_linesOf]
  by_cases he : Even S.card
  · have ho : ¬Odd S.card := Nat.not_odd_iff_even.mpr he
    rw [if_neg (by simpa using ho), Law.LS_even he]
  · have ho : Odd S.card := Nat.not_even_iff_odd.mp he
    rw [if_pos (by simpa using ho), Law.LS, Law.zS_sq, Law.signS_odd ho]
    push_cast
    ring

theorem LZ_ne_zero : ∀ S : Finset (Fin 6), Law.LZ S ≠ 0 := by
  decide +kernel

theorem LZ_values : (∀ S : Finset (Fin 6), Even S.card → Law.LZ S = 5) ∧
    (∀ t : Fin 5, Law.LZ {t.succ} = 3) ∧ Law.LZ {0} = 5 ∧
    (∀ a b : Fin 5, a ≠ b → Law.LZ (outside a b) = -1 ∧ Law.LZ {0, a.succ, b.succ} = 1) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem coinAt_one : coinAt (1 : Matrix (Fin 5) (Fin 5) ℂ) = coinC := by
  have hs : (∑ i : Fin 5, ∑ j : Fin 5, (1 : Matrix (Fin 5) (Fin 5) ℂ) i j) = 5 := by
    simp [Fin.sum_univ_five, Matrix.one_apply] <;> norm_num
  ext i j
  rw [coinC_apply, coinAt, hs]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_one, onesK, Matrix.of_apply, Matrix.one_apply,
    smul_eq_mul]
  split_ifs <;> norm_num

theorem eS_eq (S : Finset (Fin 6)) : Law.eS S = 1 - 2 / |(Law.LZ S : ℝ)| := by
  rw [Law.eS, Law.norm_wS]
  ring

theorem wS_eq (S : Finset (Fin 6)) : Law.wS S = zS S / Law.LS S := rfl

theorem plane_state_departures : ∀ s : State, (disagreeSet s.1).card = 2 →
    (s.2 ∈ disagreeSet s.1 →
      (Finset.univ.filter fun s' => Continues s s' ∧ (disagreeSet s'.1).card = 4).card = 1 ∧
      (Finset.univ.filter fun s' => Continues s s' ∧ (disagreeSet s'.1).card = 2).card = 3) ∧
    (s.2 ∉ disagreeSet s.1 →
      (Finset.univ.filter fun s' => Continues s s' ∧ (disagreeSet s'.1).card = 4).card = 2 ∧
      (Finset.univ.filter fun s' => Continues s s' ∧ (disagreeSet s'.1).card = 2).card = 2) := by
  decide +kernel

theorem LS_cases (S : Finset (Fin 6)) :
    Law.LS S = if Even S.card then 5 else 5 - 2 * (Law.linesIn S : ℂ) := by
  split_ifs with he
  · exact Law.LS_even he
  · rw [Law.LS, Law.zS_sq, Law.signS_odd (Nat.not_even_iff_odd.mp he)]
    push_cast
    ring

/-- At an even divided set: `|w_S| = 1/5`, transmission `2/5`, reflection `3/5`. -/
theorem even_step {S : Finset (Fin 6)} (he : Even S.card) :
    ‖Law.wS S‖ = 1 / 5 ∧ Law.tS S = 2 / 5 ∧ Law.eS S = 3 / 5 := by
  have hn : ‖Law.wS S‖ = 1 / 5 := by
    rw [Law.norm_wS, LZ_values.1 S he]
    norm_num
  refine ⟨hn, ?_, ?_⟩
  · rw [Law.tS, hn]
    norm_num
  · rw [Law.eS, hn]
    norm_num

/-- At a line alone: `L = 3`, `w = i/3`, reflection `1/3`. -/
theorem line_step (t : Fin 5) : Law.LS {t.succ} = 3 ∧ Law.wS {t.succ} = I / 3 ∧ Law.eS {t.succ} = 1 / 3 := by
  have hL : Law.LS {t.succ} = 3 := by
    rw [Law.LS_eq_LZ, LZ_values.2.1 t]
    norm_num
  refine ⟨hL, ?_, ?_⟩
  · rw [wS_eq, hL]
    simp [zS, Law.zS]
  · rw [eS_eq, LZ_values.2.1 t]
    norm_num

/-- At the singlet alone: `L = 5`, reflection `3/5`. -/
theorem singlet_step : Law.LS {0} = 5 ∧ Law.eS {0} = 3 / 5 := by
  have hL : Law.LS {0} = 5 := by
    rw [Law.LS_eq_LZ, LZ_values.2.2.1]
    norm_num
  refine ⟨hL, ?_⟩
  rw [eS_eq, LZ_values.2.2.1]
  norm_num

theorem I_pow_three : I ^ 3 = -I := by
  rw [pow_succ, I_sq]
  ring

/-- At the counterpart of a plane: named by its three outside lines `L = −1`, `w = i`; named `{n, a, b}` `L = 1`, `w = −i`;
`w² = −1` either way. -/
theorem twin_step {a b : Fin 5} (hab : a ≠ b) :
    Law.LS (outside a b) = -1 ∧ Law.wS (outside a b) = I ∧
    Law.LS {0, a.succ, b.succ} = 1 ∧ Law.wS {0, a.succ, b.succ} = -I ∧
    Law.wS (outside a b) ^ 2 = -1 ∧ Law.wS {0, a.succ, b.succ} ^ 2 = -1 := by
  obtain ⟨e1, e2⟩ := LZ_values.2.2.2 a b hab
  have hc3 : ∀ a b : Fin 5, a ≠ b →
      (outside a b).card = 3 ∧ ({0, a.succ, b.succ} : Finset (Fin 6)).card = 3 := by
    decide +kernel
  obtain ⟨c1, c2⟩ := hc3 a b hab
  have hz1 : zS (outside a b) = -I := by
    simp only [zS, Law.zS, c1]
    exact I_pow_three
  have hz2 : zS {0, a.succ, b.succ} = -I := by
    simp only [zS, Law.zS, c2]
    exact I_pow_three
  have hL1 : Law.LS (outside a b) = -1 := by
    rw [Law.LS_eq_LZ, e1]
    norm_num
  have hL2 : Law.LS {0, a.succ, b.succ} = 1 := by
    rw [Law.LS_eq_LZ, e2]
    norm_num
  have hw1 : Law.wS (outside a b) = I := by
    rw [wS_eq, hz1, hL1]
    ring
  have hw2 : Law.wS {0, a.succ, b.succ} = -I := by
    rw [wS_eq, hz2, hL2]
    ring
  refine ⟨hL1, hw1, hL2, hw2, ?_, ?_⟩
  · rw [hw1, I_sq]
  · rw [hw2, neg_sq, I_sq]

/-- **Proposition 44 (the step at each divided set).** On the five directions, with `q_S` the square root of the sign of the divided set:
`G_S = q_S†q_S = 1` (`S` even), `G_S = q_Sᵀq_S = θ_S` (`S` odd); `L_S = 𝟏ᵀG_S𝟏 = 5` (`S` even), `5 − 2k` (`S` odd,
`k` lines in `S`), never `0`; the coin at `S`, `σ_S = (2/L_S)𝟏𝟏ᵀG_S − I`, has `σ_S² = I` and `σ_∅ = σ₅`, Prop. 28's
coin; the reflection is `1 − 2/|L_S|` and the weight of a step `w_S = z_S/L_S`; at an even divided set `|w_S| = 1/5`; a symmetric
state continues once to a vector state and three times to symmetric states when its last-step direction is in the plane, twice and twice when
it is not; of the `200` departures from the fifty symmetric states `80` reach a vector state, `120` a plane and `12` each
plane: transmission `2|w_S| = 2/5 = 80/200`, reflection `1 − 2|w_S| = 3/5 = 120/200`, `s = 12/200 = 3/50` per plane; at
`{t}`: `L = 3`, `w = i/3`, reflection `1/3`; at `{n}`: `L = 5`, reflection `3/5`; at the counterpart of a plane named by its three
outside lines `L = −1`, `w = i`, named `{n, a, b}` `L = 1`, `w = −i`; `w² = −1` either way.

Recognition: the reflection `3/5` of the counted step gives `f = (3/5)²/10`, the reflection `1/3` of the coherent one
`α_s² = (1/3)²/8`. Uses Props. 19, 28, 29, 35, 42. -/
theorem prop_44 :
    (∀ S : Finset (Fin 6), (halfLines S)ᴴ * halfLines S = 1) ∧
    (∀ S : Finset (Fin 6),
      (halfLines S)ᵀ * halfLines S = Matrix.diagonal fun t => if t.succ ∈ S then -1 else 1) ∧
    (∀ S : Finset (Fin 6), Even S.card → GS S = 1) ∧
    (∀ S : Finset (Fin 6), Odd S.card → GS S = Matrix.diagonal fun t => if t.succ ∈ S then -1 else 1) ∧
    (∀ S : Finset (Fin 6), ∑ i, ∑ j, GS S i j = Law.LS S) ∧
    (∀ S : Finset (Fin 6), Law.LS S = if Even S.card then 5 else 5 - 2 * (Law.linesIn S : ℂ)) ∧
    (∀ S : Finset (Fin 6), Law.LS S ≠ 0) ∧
    (∀ S : Finset (Fin 6), coinAt (GS S) * coinAt (GS S) = 1) ∧
    coinAt (GS ∅) = coinC ∧
    (∀ S : Finset (Fin 6), Law.eS S = 1 - 2 / |(Law.LZ S : ℝ)|) ∧
    (∀ S : Finset (Fin 6), Law.wS S = zS S / Law.LS S) ∧
    (∀ S : Finset (Fin 6), Even S.card → ‖Law.wS S‖ = 1 / 5 ∧ Law.tS S = 2 / 5 ∧ Law.eS S = 3 / 5) ∧
    (∀ s : State, (disagreeSet s.1).card = 2 →
      (s.2 ∈ disagreeSet s.1 →
        (Finset.univ.filter fun s' => Continues s s' ∧ (disagreeSet s'.1).card = 4).card = 1 ∧
        (Finset.univ.filter fun s' => Continues s s' ∧ (disagreeSet s'.1).card = 2).card = 3) ∧
      (s.2 ∉ disagreeSet s.1 →
        (Finset.univ.filter fun s' => Continues s s' ∧ (disagreeSet s'.1).card = 4).card = 2 ∧
        (Finset.univ.filter fun s' => Continues s s' ∧ (disagreeSet s'.1).card = 2).card = 2)) ∧
    ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
        (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2).card = 200 ∧
    ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
        (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2 ∧ (disagreeSet p.2.1).card = 4).card = 80 ∧
    ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
        (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2 ∧ (disagreeSet p.2.1).card = 2).card = 120 ∧
    (∀ k : Fin 16, (disagreeSet k).card = 2 →
      ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
        (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2 ∧ p.2.1 = k).card = 12) ∧
    ((80 : ℚ) / 200 = 2 / 5 ∧ (120 : ℚ) / 200 = 3 / 5 ∧ (12 : ℚ) / 200 = 3 / 50) ∧
    (∀ t : Fin 5, Law.LS {t.succ} = 3 ∧ Law.wS {t.succ} = I / 3 ∧ Law.eS {t.succ} = 1 / 3) ∧
    (Law.LS {0} = 5 ∧ Law.eS {0} = 3 / 5) ∧
    (∀ a b : Fin 5, a ≠ b →
      Law.LS (outside a b) = -1 ∧ Law.wS (outside a b) = I ∧
      Law.LS {0, a.succ, b.succ} = 1 ∧ Law.wS {0, a.succ, b.succ} = -I ∧
      Law.wS (outside a b) ^ 2 = -1 ∧ Law.wS {0, a.succ, b.succ} ^ 2 = -1) := by
  obtain ⟨d1, d2, d3, d4⟩ := plane_departures
  refine ⟨halfLines_herm, halfLines_bil, fun S he => GS_even he, fun S ho => GS_odd ho, sum_GS, LS_cases,
    fun S => ?_, fun S => ?_, ?_, eS_eq, wS_eq, fun S he => even_step he, plane_state_departures, d1, d2, d3, d4,
    by norm_num, line_step, singlet_step, fun a b hab => twin_step hab⟩
  · rw [Law.LS_eq_LZ]
    exact_mod_cast LZ_ne_zero S
  · apply coinAt_sq
    rw [sum_GS, Law.LS_eq_LZ]
    exact_mod_cast LZ_ne_zero S
  · rw [GS_even (by simp), coinAt_one]

/-! ## Proposition 97 -/

/-- **Proposition 97 (the reflections are radar steps).** `tanh log 2 = 3/5`, `tanh(log 2/2) = 1/3`,
`tanh(log 2/4) = 3 − 2√2 = tan²(π/8)`, `cosh log 2 = 5/4`; the reflection at every even divided set is `tanh log 2` and at a
line alone `tanh(log 2/2)` (Prop. 44); `tan²(π/8)` is the half phase of the line factor at the last-step direction's phase
(Prop. 51).

Recognition: the reflection of a counted step is the speed of one radar step of rapidity `log 2` (`v = 3/5`, `γ = 5/4`);
the reflection of a step carried as an amplitude halves that rapidity, and the half phase of the line factor quarters it.
Uses Props. 44, 51. -/
theorem prop_97 :
    Real.tanh (Real.log 2) = 3 / 5 ∧ Real.tanh (Real.log 2 / 2) = 1 / 3 ∧
    Real.tanh (Real.log 2 / 4) = 3 - 2 * Real.sqrt 2 ∧ 3 - 2 * Real.sqrt 2 = Real.tan (Real.pi / 8) ^ 2 ∧
    Real.cosh (Real.log 2) = 5 / 4 ∧
    (∀ S : Finset (Fin 6), Even S.card → Law.eS S = Real.tanh (Real.log 2)) ∧
    (∀ t : Fin 5, Law.eS {t.succ} = Real.tanh (Real.log 2 / 2)) := by
  obtain ⟨r1, r2, r3, r4⟩ := Article.echoes
  refine ⟨r1, r2, r3, r4, ArticleStatements.Radar.radar_gamma.1, fun S he => ?_, fun t => ?_⟩
  · rw [r1]
    exact (even_step he).2.2
  · rw [r2]
    exact (line_step t).2.2

end Comparison.System.Existence
