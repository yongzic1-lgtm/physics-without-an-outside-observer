module

public import Comparison.Elements.Turns

/-!
# The Elements of Comparison in Lean. Book IV: divisions

In the basis `f₀ = J` (the singlet) and `f_{s+1} = i γ_s J` of P1's real six, a division is a set `D`
of divided directions (`D` and its complement are one division), and its sign `θ_D` is `−1` on `D`
and `+1` off `D`. Each generator turns the six by the matrix `rotMat (plane x)` (`gen_acts_matrix`).
A generator is **kept** by the division when its matrix commutes with `θ_D` and **moved** when it
anticommutes (Definition 15).

* `kept_iff`, `moved_iff`: kept exactly when its plane lies in `D` or outside `D`; every
  generator is kept or moved, never both.
* `card_kept`, `card_moved`: `C(k,2) + C(6−k,2)` kept and `k(6−k)` moved, `k = |D|`;
  `four_kinds`: `15/0, 10/5, 7/8, 6/9` for `k = 0, 1, 2, 3`; `card_kept_compl`: a division and
  its complement count the same.
* `card_kept_ten`, `card_moved_ten`: with the singlet fixed, among the ten that keep the singlet,
  `C(r,2) + C(5−r,2)` kept and `r(5−r)` moved, `r` the number of divided lines;
  `six_divisions`: point, line, plane, each without and with the singlet: `10/0, 10/0, 6/4, 6/4, 4/6,
  4/6`.
* `P3_division_keeps_ten`: P3's own division (the five directions against the singlet) keeps exactly the
  ten symmetric states and moves the five `i γ_s`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-- The sign of a division: `−1` on the divided directions, `+1` on the others. -/
def divSign (D : Finset (Fin 6)) : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.diagonal fun c => if c ∈ D then -1 else 1

/-- The rotation of the plane `p` on the six, doubled: column `p.1` is `2 f_{p.2}`, column `p.2`
is `−2 f_{p.1}`. -/
def rotMat (p : Fin 6 × Fin 6) : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun d c => if d = p.2 ∧ c = p.1 then 2 else if d = p.1 ∧ c = p.2 then -2 else 0

theorem rotSix_eq_sum (p : Fin 6 × Fin 6) (hp : p.1 ≠ p.2) (c : Fin 6) :
    rotSix p c = ∑ d, ((rotMat p d c : ℤ) : ℂ) • sixP1 d := by
  simp only [rotSix, rotMat, Matrix.of_apply]
  by_cases h1 : c = p.1
  · subst h1
    simp [hp]
  · by_cases h2 : c = p.2
    · subst h2
      simp [h1]
    · simp [h1, h2]

/-- **The matrix of each generator on P1's real six is the rotation of its plane.** -/
theorem gen_acts_matrix (x : Fin 5 ⊕ Fin 10) (c : Fin 6) :
    act (gen x) (sixP1 c) = ∑ d, ((rotMat (plane x) d c : ℤ) : ℂ) • sixP1 d := by
  rw [gen_acts, rotSix_eq_sum _ (ne_of_lt (plane_lt x))]

/-- The plane rotation commutes with the sign exactly when the plane lies in one part. -/
theorem rot_comm_iff (D : Finset (Fin 6)) (p : Fin 6 × Fin 6) (hp : p.1 ≠ p.2) :
    rotMat p * divSign D = divSign D * rotMat p ↔ (p.1 ∈ D ↔ p.2 ∈ D) := by
  rw [← Matrix.ext_iff]
  simp only [divSign, Matrix.mul_diagonal, Matrix.diagonal_mul, rotMat, Matrix.of_apply]
  constructor
  · intro h
    have h1 := h p.2 p.1
    simp only [and_self, ite_true] at h1
    by_cases ha : p.1 ∈ D <;> by_cases hb : p.2 ∈ D <;> simp_all
  · intro h d c
    by_cases h1 : d = p.2 ∧ c = p.1
    · obtain ⟨rfl, rfl⟩ := h1
      by_cases ha : p.1 ∈ D <;> simp_all
    · by_cases h2 : d = p.1 ∧ c = p.2
      · obtain ⟨rfl, rfl⟩ := h2
        by_cases ha : p.1 ∈ D <;> simp_all
      · simp [h1, h2]

/-- The plane rotation anticommutes with the sign exactly when the plane joins the two parts. -/
theorem rot_anticomm_iff (D : Finset (Fin 6)) (p : Fin 6 × Fin 6) (hp : p.1 ≠ p.2) :
    rotMat p * divSign D = -(divSign D * rotMat p) ↔ ¬(p.1 ∈ D ↔ p.2 ∈ D) := by
  rw [← Matrix.ext_iff]
  simp only [divSign, Matrix.mul_diagonal, Matrix.diagonal_mul, rotMat, Matrix.of_apply,
    Matrix.neg_apply]
  constructor
  · intro h
    have h1 := h p.2 p.1
    simp only [and_self, ite_true] at h1
    by_cases ha : p.1 ∈ D <;> by_cases hb : p.2 ∈ D <;> simp_all
  · intro h d c
    by_cases h1 : d = p.2 ∧ c = p.1
    · obtain ⟨rfl, rfl⟩ := h1
      by_cases ha : p.1 ∈ D <;> simp_all
    · by_cases h2 : d = p.1 ∧ c = p.2
      · obtain ⟨rfl, rfl⟩ := h2
        by_cases ha : p.1 ∈ D <;> simp_all
      · simp [h1, h2]

/-- A generator is **kept** by the division `D` when its rotation commutes with the sign. -/
def Kept (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) : Prop :=
  rotMat (plane x) * divSign D = divSign D * rotMat (plane x)

/-- A generator is **moved** by the division `D` when its rotation anticommutes with the sign. -/
def Moved (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) : Prop :=
  rotMat (plane x) * divSign D = -(divSign D * rotMat (plane x))

theorem kept_iff (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) :
    Kept D x ↔ ((plane x).1 ∈ D ↔ (plane x).2 ∈ D) :=
  rot_comm_iff D _ (ne_of_lt (plane_lt x))

theorem moved_iff (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) :
    Moved D x ↔ ¬((plane x).1 ∈ D ↔ (plane x).2 ∈ D) :=
  rot_anticomm_iff D _ (ne_of_lt (plane_lt x))

instance (D : Finset (Fin 6)) : DecidablePred (Kept D) :=
  fun x => decidable_of_iff _ (kept_iff D x).symm

instance (D : Finset (Fin 6)) : DecidablePred (Moved D) :=
  fun x => decidable_of_iff _ (moved_iff D x).symm

/-- Every generator is kept or moved, and not both. -/
theorem kept_xor_moved (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) : Kept D x ↔ ¬Moved D x := by
  rw [kept_iff, moved_iff, not_not]

theorem card_kept_plane : ∀ D : Finset (Fin 6),
    (Finset.univ.filter fun x : Fin 5 ⊕ Fin 10 => ((plane x).1 ∈ D ↔ (plane x).2 ∈ D)).card =
      D.card.choose 2 + (6 - D.card).choose 2 := by
  decide +kernel

theorem card_moved_plane : ∀ D : Finset (Fin 6),
    (Finset.univ.filter fun x : Fin 5 ⊕ Fin 10 => ¬((plane x).1 ∈ D ↔ (plane x).2 ∈ D)).card =
      D.card * (6 - D.card) := by
  decide +kernel

/-- **Kept rotations of a division:** `C(k,2) + C(6−k,2)`, `k` the number of divided directions. -/
theorem card_kept (D : Finset (Fin 6)) :
    (Finset.univ.filter (Kept D)).card = D.card.choose 2 + (6 - D.card).choose 2 := by
  rw [← card_kept_plane D]
  exact congrArg Finset.card (Finset.filter_congr fun x _ => kept_iff D x)

/-- **Moved rotations of a division:** `k (6 − k)`. -/
theorem card_moved (D : Finset (Fin 6)) :
    (Finset.univ.filter (Moved D)).card = D.card * (6 - D.card) := by
  rw [← card_moved_plane D]
  exact congrArg Finset.card (Finset.filter_congr fun x _ => moved_iff D x)

/-- A division and its complement keep and move the same rotations. -/
theorem kept_compl (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) : Kept Dᶜ x ↔ Kept D x := by
  rw [kept_iff, kept_iff, Finset.mem_compl, Finset.mem_compl, not_iff_not]

theorem card_kept_compl (D : Finset (Fin 6)) :
    (Finset.univ.filter (Kept Dᶜ)).card = (Finset.univ.filter (Kept D)).card :=
  congrArg Finset.card (Finset.filter_congr fun x _ => kept_compl D x)

/-- **The four types of division under the fifteen rotations**, by the size `k` of the smaller part:
kept/moved `15/0, 10/5, 7/8, 6/9`. -/
theorem four_kinds (D : Finset (Fin 6)) :
    (D.card = 0 → (Finset.univ.filter (Kept D)).card = 15 ∧
        (Finset.univ.filter (Moved D)).card = 0) ∧
    (D.card = 1 → (Finset.univ.filter (Kept D)).card = 10 ∧
        (Finset.univ.filter (Moved D)).card = 5) ∧
    (D.card = 2 → (Finset.univ.filter (Kept D)).card = 7 ∧
        (Finset.univ.filter (Moved D)).card = 8) ∧
    (D.card = 3 → (Finset.univ.filter (Kept D)).card = 6 ∧
        (Finset.univ.filter (Moved D)).card = 9) := by
  rw [card_kept, card_moved]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] <;> decide

/-! ## With the singlet fixed: the ten -/

theorem card_kept_ten_plane : ∀ D : Finset (Fin 6),
    (Finset.univ.filter fun f : Fin 10 =>
        ((plane (Sum.inr f)).1 ∈ D ↔ (plane (Sum.inr f)).2 ∈ D)).card =
      (D.erase 0).card.choose 2 + (5 - (D.erase 0).card).choose 2 := by
  decide +kernel

theorem card_moved_ten_plane : ∀ D : Finset (Fin 6),
    (Finset.univ.filter fun f : Fin 10 =>
        ¬((plane (Sum.inr f)).1 ∈ D ↔ (plane (Sum.inr f)).2 ∈ D)).card =
      (D.erase 0).card * (5 - (D.erase 0).card) := by
  decide +kernel

/-- **With the singlet fixed**, among the ten rotations that keep the singlet, a division keeps
`C(r,2) + C(5−r,2)`, `r` the number of divided lines. -/
theorem card_kept_ten (D : Finset (Fin 6)) :
    (Finset.univ.filter fun f : Fin 10 => Kept D (Sum.inr f)).card =
      (D.erase 0).card.choose 2 + (5 - (D.erase 0).card).choose 2 := by
  rw [← card_kept_ten_plane D]
  exact congrArg Finset.card (Finset.filter_congr fun f _ => kept_iff D _)

/-- ... and moves `r (5 − r)`. -/
theorem card_moved_ten (D : Finset (Fin 6)) :
    (Finset.univ.filter fun f : Fin 10 => Moved D (Sum.inr f)).card =
      (D.erase 0).card * (5 - (D.erase 0).card) := by
  rw [← card_moved_ten_plane D]
  exact congrArg Finset.card (Finset.filter_congr fun f _ => moved_iff D _)

/-- **Six divisions with the singlet fixed**: point `∅`, point with the singlet `{0}`, line `{1}`,
line with the singlet `{0, 1}`, plane `{1, 2}`, plane with the singlet `{0, 1, 2}`; under the fifteen
they are of types `0, 1, 1, 2, 2, 3`, and among the ten they keep/move `10/0, 10/0, 6/4, 6/4,
4/6, 4/6`. -/
theorem six_divisions :
    [(∅ : Finset (Fin 6)), {0}, {1}, {0, 1}, {1, 2}, {0, 1, 2}].map
      (fun D => ((Finset.univ.filter (Kept D)).card, (Finset.univ.filter (Moved D)).card,
        (Finset.univ.filter fun f : Fin 10 => Kept D (Sum.inr f)).card,
        (Finset.univ.filter fun f : Fin 10 => Moved D (Sum.inr f)).card)) =
    [(15, 0, 10, 0), (10, 5, 10, 0), (10, 5, 6, 4), (7, 8, 6, 4), (7, 8, 4, 6), (6, 9, 4, 6)] := by
  simp only [List.map_cons, List.map_nil, card_kept, card_moved, card_kept_ten, card_moved_ten]
  decide

/-- **P3's own division**, the five directions divided and the singlet undivided, keeps exactly the ten symmetric
states and moves the five `i γ_s`, which turn the singlet into the lines. -/
theorem P3_division_keeps_ten (x : Fin 5 ⊕ Fin 10) :
    Kept {1, 2, 3, 4, 5} x ↔ x.isRight := by
  rw [kept_iff]
  revert x
  decide

end Comparison

end
