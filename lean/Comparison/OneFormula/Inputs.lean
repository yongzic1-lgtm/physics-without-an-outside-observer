import Comparison.Mass.Angle
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# OneFormula: explicit source inputs and a complete two-root readout

The physical source assignments are inputs. The results
here concern the common clock functional, its additive completion, and the
algebraic information retained by both roots of the one-level kernel.
-/

namespace Comparison.OneFormula

open Matrix

noncomputable def clockRate (X : Matrix State State ℝ) : ℝ :=
  (1 / 320) * ∑ s : State, ∑ t : State, if Continues s t then X t s else 0

theorem clockRate_is_law (X : Matrix State State ℝ) :
    clockRate X = piU ⬝ᵥ (hadPow lawP X 1 *ᵥ 1) := by
  exact (lawP_rate X).symm

theorem clockRate_add (X Y : Matrix State State ℝ) :
    clockRate (X + Y) = clockRate X + clockRate Y := by
  unfold clockRate
  have he : ∀ s t : State,
      (if Continues s t then (X + Y) t s else 0) =
      (if Continues s t then X t s else 0) +
      (if Continues s t then Y t s else 0) := by
    intro s t
    split_ifs <;> simp
  simp_rw [he, Finset.sum_add_distrib]
  ring

theorem clockRate_smul (a : ℝ) (X : Matrix State State ℝ) :
    clockRate (a • X) = a * clockRate X := by
  unfold clockRate
  have he : ∀ s t : State,
      (if Continues s t then (a • X) t s else 0) =
      a * (if Continues s t then X t s else 0) := by
    intro s t
    split_ifs <;> simp
  simp_rw [he, ← Finset.mul_sum]
  ring

theorem electron_rate (s t : State) (h : Continues s t) :
    clockRate (oneTransitionX s t) = 1 / 320 := by
  rw [clockRate_is_law]
  exact one_transition_angle_rate s t h

theorem availableTransitions_rate (h : Fin 5) :
    clockRate (availableTransitionsLawX h (transitionX h)) = 1836 / 320 := by
  rw [clockRate_is_law]
  exact availableTransitions_angle_rate h

theorem completed_availableTransitions_ratio (h : Fin 5) (s t : State)
    (hst : Continues s t) (boundary : ℝ) :
    clockRate (availableTransitionsLawX h (transitionX h) + boundary • oneTransitionX s t) /
      clockRate (oneTransitionX s t) = 1836 + boundary := by
  rw [clockRate_add, clockRate_smul, availableTransitions_rate, electron_rate s t hst]
  ring

theorem unit_source_ratio (s t : State) (hst : Continues s t) (amplitude : ℝ) :
    clockRate (amplitude • oneTransitionX s t) / clockRate (oneTransitionX s t) = amplitude := by
  rw [clockRate_smul, electron_rate s t hst]
  ring

theorem root_polynomial (S : ℝ) :
    4 * ((3 + Real.sqrt (9 + 16 * Real.exp (-S))) / 8) ^ 2 -
      3 * ((3 + Real.sqrt (9 + 16 * Real.exp (-S))) / 8) = Real.exp (-S) := by
  have hs : 0 ≤ 9 + 16 * Real.exp (-S) := by positivity
  have sq := Real.sq_sqrt hs
  nlinarith

theorem plus_root_positive (S : ℝ) :
    0 < (3 + Real.sqrt (9 + 16 * Real.exp (-S))) / 8 := by
  positivity

theorem stable_minus_product (S p : ℝ) (hp : p ≠ 0) :
    p * (-Real.exp (-S) / (4*p)) = -Real.exp (-S) / 4 := by
  field_simp

theorem both_root_log (S p : ℝ) (hp : 0 < p) :
    -Real.log p - Real.log (Real.exp (-S)/(4*p)) - Real.log 4 = S := by
  rw [Real.log_div (Real.exp_ne_zero _) (by positivity),
      Real.log_exp, Real.log_mul (by norm_num) (ne_of_gt hp)]
  ring

theorem both_modes_forget_overlap (S T c : ℝ) :
    (S + T + Real.sqrt ((S-T)^2 + 4*c*S*T))/2 +
      (S + T - Real.sqrt ((S-T)^2 + 4*c*S*T))/2 = S + T := by
  ring

theorem matched_whole_readout (S T c : ℝ) :
    ((S + T + Real.sqrt ((S-T)^2 + 4*c*S*T))/2 +
      (S + T - Real.sqrt ((S-T)^2 + 4*c*S*T))/2)/5 = (S+T)/5 := by
  rw [both_modes_forget_overlap]

theorem squared_mass_ratio (rho delta : ℝ) :
    6 * rho^2 * delta / rho^2 = 6*delta ∨ rho = 0 := by
  by_cases h : rho = 0
  · exact Or.inr h
  · left
    field_simp

#print axioms clockRate_is_law
#print axioms clockRate_add
#print axioms clockRate_smul
#print axioms electron_rate
#print axioms availableTransitions_rate
#print axioms completed_availableTransitions_ratio
#print axioms unit_source_ratio
#print axioms root_polynomial
#print axioms plus_root_positive
#print axioms stable_minus_product
#print axioms both_root_log
#print axioms both_modes_forget_overlap
#print axioms matched_whole_readout
#print axioms squared_mass_ratio

end Comparison.OneFormula
