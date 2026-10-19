import Comparison.Law.Returns

/-!
# The level of a line inside a plane meeting's return

Proposition 175 (cell 5) asks how the levels of the lines
meeting at a plane move a vector's pole, given that the plane meeting's factor has no zero on
`|u| = 1/4` (Propositions 150, 152). The joint walk answers the first half exactly. A level is a weight
`w_t = e^{−S_t}` on the steps along a line `t` (Definition 43), the same weight in every channel of the
joint walk, since it rides on the step and not on the transported operator.

* `jointWalkW`: the joint walk at a pattern `P` with a weight `w_s` on every step along `s`.
* `jointWalkW_channel`: an operator carried by every step with the signs `c_s` is a channel on which the
  weighted joint walk is `diag(ε(P) w c)(𝐉 − I)`.
* `vector_channel_F`: **at the plane meeting `F`, on the plane's rotation (the meeting's own element), the
  weighted joint walk is `diag(w)(𝐉 − I)` for every weight `w`**;
* `scalar_channel_singlet`: at the singlet, on the scalar channel, it is the same `diag(w)(𝐉 − I)`;
* `vector_equals_pseudoscalar`: the two are one operator for every weight; so their determinants, the
  zero near `1/4` and its shift by the levels are one function of the levels (Proposition 135 at `U = ∅`,
  Proposition 140), to every order: `level_determinant`.
* `scalar_channel_F`: at `F` the scalar channel carries `diag(ε(F) w)(𝐉 − I)`, the plane meeting's own
  factor, which is the one with no zero on `|u| = 1/4`; `colour_channel_C`: at `C` the plane's rotation carries
  `−diag(w)(𝐉 − I)`.

Reading (not a theorem): a vector lands at a plane meeting (Proposition 175's table) with the plane's rotation
as its own element there; read on that channel its pole moves under the levels exactly as the
pseudoscalar's at the singlet, so `M_V² − M_P²` does not depend on the levels. The level-free part of the
vector is not given by this channel: it is what the vertex still asks.
-/

open Comparison Matrix Kronecker
open Comparison.Law

namespace Comparison.JointCells.Places

/-- The agreement sign `ε_s(P)`. -/
def agr (P : Finset (Fin 5)) (s : Fin 5) : ℂ := if s ∈ P then -1 else 1

/-- `𝐉 − I` on the five directions. -/
def offD : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun i j => if i = j then 0 else 1

/-- The plane `F = {h, k}`, its colour counterpart `C`, and the plane's rotation `γ_hγ_k`. -/
def planeF : Finset (Fin 5) := {0, 1}
def colourC : Finset (Fin 5) := {2, 3, 4}
def planeTurn : Matrix Four Four ℂ := γ 0 * γ 1

/-- **The weighted joint walk:** the last-step direction arrives at `s` with `ε_s(P) w_s` and the step along `s`
carries one system's operators. -/
noncomputable def jointWalkW (P : Finset (Fin 5)) (w : Fin 5 → ℂ)
    (v : Fin 5 → Matrix Four Four ℂ) : Fin 5 → Matrix Four Four ℂ :=
  fun s => (agr P s * w s) • (γ s * (∑ t, (if s = t then (0 : ℂ) else 1) • v t) * γ s)

theorem jointWalkW_channel (P : Finset (Fin 5)) (w : Fin 5 → ℂ) (X : Matrix Four Four ℂ)
    (c : Fin 5 → ℂ) (hc : ∀ s, γ s * X * γ s = c s • X) (a : Fin 5 → ℂ) :
    jointWalkW P w (fun t => a t • X) =
      fun s => ((diagonal (fun s => agr P s * w s * c s) * offD) *ᵥ a) s • X := by
  funext s
  simp only [jointWalkW]
  have hsum : (∑ t, (if s = t then (0 : ℂ) else 1) • (a t • X)) =
      (∑ t, (if s = t then (0 : ℂ) else 1) * a t) • X := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun t _ => by rw [smul_smul]
  rw [hsum, Matrix.mul_smul, Matrix.smul_mul, hc s, smul_smul, smul_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, diagonal_mul, offD, of_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- The step carries the plane's rotation with the plane's agreement sign (`γ_conj_relOp` at the plane). -/
theorem step_planeTurn (s : Fin 5) : γ s * planeTurn * γ s = agr planeF s • planeTurn := by
  have h := γ_conj_relOp s 6
  have e1 : relOp 6 = planeTurn := rfl
  have e2 : disagreeSet 6 = planeF := rfl
  rw [e1, e2] at h
  rw [h]
  rfl

theorem agr_sq (P : Finset (Fin 5)) (s : Fin 5) : agr P s * agr P s = 1 := by
  unfold agr
  split_ifs <;> norm_num

/-- **The vector's channel at the plane meeting:** on the plane's rotation the weighted joint walk at `F` is
`diag(w)(𝐉 − I)`, for every weight on the steps. -/
theorem vector_channel_F (w : Fin 5 → ℂ) (a : Fin 5 → ℂ) :
    jointWalkW planeF w (fun t => a t • planeTurn) =
      fun s => ((diagonal w * offD) *ᵥ a) s • planeTurn := by
  rw [jointWalkW_channel planeF w planeTurn (agr planeF) step_planeTurn]
  have h : (fun s => agr planeF s * w s * agr planeF s) = w := by
    funext s
    rw [mul_comm (agr planeF s) (w s), mul_assoc, agr_sq, mul_one]
  rw [h]

/-- **The pseudoscalar's channel at the singlet:** on the scalar channel the weighted joint walk at the
singlet is `diag(w)(𝐉 − I)`. -/
theorem scalar_channel_singlet (w : Fin 5 → ℂ) (a : Fin 5 → ℂ) :
    jointWalkW ∅ w (fun t => a t • (1 : Matrix Four Four ℂ)) =
      fun s => ((diagonal w * offD) *ᵥ a) s • (1 : Matrix Four Four ℂ) := by
  rw [jointWalkW_channel ∅ w 1 (fun _ => 1)
    (fun s => by rw [Matrix.mul_one, γ_mul_self, one_smul])]
  have h : (fun s => agr ∅ s * w s * 1) = w := by
    funext s
    simp [agr]
  rw [h]

/-- **One operator for every level:** the vector's channel at `F` and the pseudoscalar's at the singlet carry
the same five-line walk. -/
theorem vector_equals_pseudoscalar (w : Fin 5 → ℂ) (a : Fin 5 → ℂ) (s : Fin 5) :
    (∃ M : Matrix (Fin 5) (Fin 5) ℂ,
      jointWalkW planeF w (fun t => a t • planeTurn) s = (M *ᵥ a) s • planeTurn ∧
      jointWalkW ∅ w (fun t => a t • (1 : Matrix Four Four ℂ)) s =
        (M *ᵥ a) s • (1 : Matrix Four Four ℂ) ∧ M = diagonal w * offD) :=
  ⟨diagonal w * offD, by rw [vector_channel_F], by rw [scalar_channel_singlet], rfl⟩

/-- **The law on the common channel** (Proposition 135 at `U = ∅`, with the Euler completion):
`det(I − u diag(w)(𝐉 − I)) = ∏_t (1 + uw_t) − u Σ_t w_t ∏_{s≠t} (1 + uw_s)`; with one level `e^{−S}` on
one line and the others one it vanishes where `1 − 3u − 4u²e^{−S} = 0` (Proposition 140), at the
same `u` for the vector's channel and the pseudoscalar's. -/
theorem level_determinant (u : ℂ) (w : Fin 5 → ℂ) :
    (1 - u • (diagonal w * offD)).det =
      ∏ t, (1 + u * w t) - u * ∑ t, w t * ∏ s ∈ Finset.univ.erase t, (1 + u * w s) :=
  euler_completion u w

/-- With one level on the line `0` (`w = (r, 1, 1, 1, 1)`): `det = (1 + u)³(1 − 3u − 4u²r)`. -/
theorem one_level (u r : ℂ) :
    (1 - u • (diagonal ![r, 1, 1, 1, 1] * offD)).det = (1 + u) ^ 3 * (1 - 3 * u - 4 * u ^ 2 * r) := by
  rw [level_determinant]
  simp only [prod_erase_ite, Fin.prod_univ_five, Fin.sum_univ_five]
  simp
  ring

/-- **At `F` the scalar channel is the plane meeting's own walk** `diag(ε(F) w)(𝐉 − I)`. -/
theorem scalar_channel_F (w : Fin 5 → ℂ) (a : Fin 5 → ℂ) :
    jointWalkW planeF w (fun t => a t • (1 : Matrix Four Four ℂ)) =
      fun s => ((diagonal (fun s => agr planeF s * w s) * offD) *ᵥ a) s •
        (1 : Matrix Four Four ℂ) := by
  rw [jointWalkW_channel planeF w 1 (fun _ => 1)
    (fun s => by rw [Matrix.mul_one, γ_mul_self, one_smul])]
  simp only [mul_one]

/-- At `C` the plane's rotation carries `−diag(w)(𝐉 − I)`: the singlet's counterpart `{n}`'s walk, for every weight. -/
theorem colour_channel_C (w : Fin 5 → ℂ) (a : Fin 5 → ℂ) :
    jointWalkW colourC w (fun t => a t • planeTurn) =
      fun s => ((diagonal (fun s => -w s) * offD) *ᵥ a) s • planeTurn := by
  rw [jointWalkW_channel colourC w planeTurn (agr planeF) step_planeTurn]
  have h : (fun s => agr colourC s * w s * agr planeF s) = fun s => -w s := by
    funext s
    fin_cases s <;> simp [agr, colourC, planeF]
  rw [h]

end Comparison.JointCells.Places

#print axioms Comparison.JointCells.Places.jointWalkW_channel
#print axioms Comparison.JointCells.Places.step_planeTurn
#print axioms Comparison.JointCells.Places.agr_sq
#print axioms Comparison.JointCells.Places.vector_channel_F
#print axioms Comparison.JointCells.Places.scalar_channel_singlet
#print axioms Comparison.JointCells.Places.vector_equals_pseudoscalar
#print axioms Comparison.JointCells.Places.level_determinant
#print axioms Comparison.JointCells.Places.one_level
#print axioms Comparison.JointCells.Places.scalar_channel_F
#print axioms Comparison.JointCells.Places.colour_channel_C
