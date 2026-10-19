module

public import Comparison.Law.Composite

/-! Three distinct vertices and one clock. The two-spinor states of the pairs compose by symmetric difference.
This is a record theorem, not a choice of coherent three-line source. -/

@[expose] public section

namespace Comparison.JointCells

open Comparison.Law

def distinctRecords : Finset (Fin 16 × Fin 16) :=
  Finset.univ.filter fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2

def recordFlags (r : Fin 5) (p : Fin 16 × Fin 16) : Bool × Bool × Bool :=
  let a := decide (r ∈ disagreeSet p.1)
  let b := decide (r ∈ disagreeSet p.2)
  (a, b, xor a b)

def flagCount (r : Fin 5) (flags : Bool × Bool × Bool) : ℕ :=
  (distinctRecords.filter fun p => recordFlags r p = flags).card

set_option maxRecDepth 4096 in
/-- The flags are the actual moved own clocks of the three pair divisions. -/
theorem recordFlags_are_moved_clocks : ∀ (r : Fin 5) (p : Fin 16 × Fin 16),
    recordFlags r p =
      (movesTurn (relDiv p.1) 0 r.succ,
       movesTurn (relDiv p.2) 0 r.succ,
       movesTurn (symmDiff (relDiv p.1) (relDiv p.2)) 0 r.succ) := by
  decide

set_option maxRecDepth 4096 in
theorem distinct_record_count : distinctRecords.card = 210 := by decide

theorem xor_triangle_counts : ∀ r : Fin 5,
    flagCount r (false, false, false) = 42 ∧
    flagCount r (false, true, true) = 56 ∧
    flagCount r (true, false, true) = 56 ∧
    flagCount r (true, true, false) = 56 ∧
    flagCount r (true, true, true) = 0 := by decide

theorem no_triple_clock (r : Fin 5) (p : Fin 16 × Fin 16) :
    recordFlags r p ≠ (true, true, true) := by
  unfold recordFlags
  cases decide (r ∈ disagreeSet p.1) <;>
    cases decide (r ∈ disagreeSet p.2) <;> decide

theorem triangle_probabilities :
    (42 : ℚ) / 210 = 1 / 5 ∧ (56 : ℚ) / 210 = 4 / 15 ∧
      (112 : ℚ) / 210 = 8 / 15 := by norm_num

theorem triangle_third_cumulant :
    (0 : ℚ) - 3 * (4 / 15) * (8 / 15) + 2 * (8 / 15) ^ 3 = -416 / 3375 := by
  norm_num

theorem two_unit_locks_det :
    Matrix.det (!![(1 : ℚ), 1, 0; 1, 1, 1; 0, 1, 1]) = -1 := by
  norm_num [Matrix.det_fin_three]

end Comparison.JointCells

#print axioms Comparison.JointCells.distinct_record_count
#print axioms Comparison.JointCells.recordFlags_are_moved_clocks
#print axioms Comparison.JointCells.xor_triangle_counts
#print axioms Comparison.JointCells.no_triple_clock
#print axioms Comparison.JointCells.triangle_probabilities
#print axioms Comparison.JointCells.triangle_third_cumulant
#print axioms Comparison.JointCells.two_unit_locks_det

end
