import Comparison.Article.Numerics

/-!
# The clock at `{h, n}` and its overlap `h`

The ten gaps of the marks `(0, 1, 2, 3, 19)/4`, the rate `ν = 9/4000`, the clock
`M_Q(x) = (1/10) Σ_D e^{-xD}` at `x = ±ν`, and `h = [M_Q(ν) M_Q(-ν)]^{-3/2}`, each with a closed interval
whose endpoints carry twenty-six significant digits.
-/

namespace Comparison.Article

open Real

/-- The clock at the tilt `+ν`: `M_Q(ν) = (1/10) Σ_D e^{-νD}` over the ten gaps. -/
noncomputable def qMQp : ℝ :=
  (((1 : ℝ) / 10) * ((((((((((Real.exp (-((9 : ℝ) / 16000))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((27 : ℝ) / 16000)))) + (Real.exp (-((171 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((81 : ℝ) / 8000)))) + (Real.exp (-((9 : ℝ) / 16000)))) + (Real.exp (-((153 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 1000)))))

theorem qMQp_bnd : Bnd qMQp (9.9551971104533484997815429e-1 : ℝ) (9.9551971104533484997815438e-1 : ℝ) := by
  unfold qMQp
  have h1 : Bnd ((1 : ℝ) / 10) ((1 : ℝ) / 10) ((1 : ℝ) / 10) := Bnd.const _
  have h2 : Bnd (-((9 : ℝ) / 16000)) (-((9 : ℝ) / 16000)) (-((9 : ℝ) / 16000)) := Bnd.const _
  have h3 : Bnd ((Real.exp (-((9 : ℝ) / 16000)))) (9.9943765817346608496472466e-1 : ℝ) (9.9943765817346608496472467e-1 : ℝ) := Bnd.exp h2 (exp_ge' (-((9 : ℝ) / 16000)) (((9 : ℝ) / 16000)) (9.9943765817346608496472466e-1 : ℝ) 8 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-((9 : ℝ) / 16000)) (((9 : ℝ) / 16000)) (9.9943765817346608496472467e-1 : ℝ) 8 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h4 : Bnd (-((9 : ℝ) / 8000)) (-((9 : ℝ) / 8000)) (-((9 : ℝ) / 8000)) := Bnd.const _
  have h5 : Bnd ((Real.exp (-((9 : ℝ) / 8000)))) (9.9887563257526203942923734e-1 : ℝ) (9.9887563257526203942923735e-1 : ℝ) := Bnd.exp h4 (exp_ge' (-((9 : ℝ) / 8000)) (((9 : ℝ) / 8000)) (9.9887563257526203942923734e-1 : ℝ) 9 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-((9 : ℝ) / 8000)) (((9 : ℝ) / 8000)) (9.9887563257526203942923735e-1 : ℝ) 9 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h6 := Bnd.add h3 h5
  have h7 : Bnd (((Real.exp (-((9 : ℝ) / 16000))) + (Real.exp (-((9 : ℝ) / 8000))))) (1.998313290748728124393962 : ℝ) (1.9983132907487281243939621 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd (-((27 : ℝ) / 16000)) (-((27 : ℝ) / 16000)) (-((27 : ℝ) / 16000)) := Bnd.const _
  have h9 : Bnd ((Real.exp (-((27 : ℝ) / 16000)))) (9.9831392302755944677295412e-1 : ℝ) (9.9831392302755944677295413e-1 : ℝ) := Bnd.exp h8 (exp_ge' (-((27 : ℝ) / 16000)) (((27 : ℝ) / 16000)) (9.9831392302755944677295412e-1 : ℝ) 10 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-((27 : ℝ) / 16000)) (((27 : ℝ) / 16000)) (9.9831392302755944677295413e-1 : ℝ) 10 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h10 := Bnd.add h7 h9
  have h11 : Bnd ((((Real.exp (-((9 : ℝ) / 16000))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((27 : ℝ) / 16000))))) (2.9966272137762875711669161 : ℝ) (2.9966272137762875711669163 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 : Bnd (-((171 : ℝ) / 16000)) (-((171 : ℝ) / 16000)) (-((171 : ℝ) / 16000)) := Bnd.const _
  have h13 : Bnd ((Real.exp (-((171 : ℝ) / 16000)))) (9.8936940841147593936675291e-1 : ℝ) (9.8936940841147593936675292e-1 : ℝ) := Bnd.exp h12 (exp_ge' (-((171 : ℝ) / 16000)) (((171 : ℝ) / 16000)) (9.8936940841147593936675291e-1 : ℝ) 12 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-((171 : ℝ) / 16000)) (((171 : ℝ) / 16000)) (9.8936940841147593936675292e-1 : ℝ) 12 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h14 := Bnd.add h11 h13
  have h15 : Bnd (((((Real.exp (-((9 : ℝ) / 16000))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((27 : ℝ) / 16000)))) + (Real.exp (-((171 : ℝ) / 16000))))) (3.985996622187763510533669 : ℝ) (3.9859966221877635105336693 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 : Bnd (-((9 : ℝ) / 16000)) (-((9 : ℝ) / 16000)) (-((9 : ℝ) / 16000)) := Bnd.const _
  have h17 : Bnd ((Real.exp (-((9 : ℝ) / 16000)))) (9.9943765817346608496472466e-1 : ℝ) (9.9943765817346608496472467e-1 : ℝ) := Bnd.exp h16 (exp_ge' (-((9 : ℝ) / 16000)) (((9 : ℝ) / 16000)) (9.9943765817346608496472466e-1 : ℝ) 8 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-((9 : ℝ) / 16000)) (((9 : ℝ) / 16000)) (9.9943765817346608496472467e-1 : ℝ) 8 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h18 := Bnd.add h15 h17
  have h19 : Bnd ((((((Real.exp (-((9 : ℝ) / 16000))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((27 : ℝ) / 16000)))) + (Real.exp (-((171 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 16000))))) (4.9854342803612295954983936 : ℝ) (4.985434280361229595498394 : ℝ) := h18.weak (by norm_num) (by norm_num)
  have h20 : Bnd (-((9 : ℝ) / 8000)) (-((9 : ℝ) / 8000)) (-((9 : ℝ) / 8000)) := Bnd.const _
  have h21 : Bnd ((Real.exp (-((9 : ℝ) / 8000)))) (9.9887563257526203942923734e-1 : ℝ) (9.9887563257526203942923735e-1 : ℝ) := Bnd.exp h20 (exp_ge' (-((9 : ℝ) / 8000)) (((9 : ℝ) / 8000)) (9.9887563257526203942923734e-1 : ℝ) 9 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-((9 : ℝ) / 8000)) (((9 : ℝ) / 8000)) (9.9887563257526203942923735e-1 : ℝ) 9 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h22 := Bnd.add h19 h21
  have h23 : Bnd (((((((Real.exp (-((9 : ℝ) / 16000))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((27 : ℝ) / 16000)))) + (Real.exp (-((171 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 8000))))) (5.9843099129364916349276309 : ℝ) (5.9843099129364916349276314 : ℝ) := h22.weak (by norm_num) (by norm_num)
  have h24 : Bnd (-((81 : ℝ) / 8000)) (-((81 : ℝ) / 8000)) (-((81 : ℝ) / 8000)) := Bnd.const _
  have h25 : Bnd ((Real.exp (-((81 : ℝ) / 8000)))) (9.8992608525439146195671703e-1 : ℝ) (9.8992608525439146195671704e-1 : ℝ) := Bnd.exp h24 (exp_ge' (-((81 : ℝ) / 8000)) (((81 : ℝ) / 8000)) (9.8992608525439146195671703e-1 : ℝ) 12 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-((81 : ℝ) / 8000)) (((81 : ℝ) / 8000)) (9.8992608525439146195671704e-1 : ℝ) 12 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h26 := Bnd.add h23 h25
  have h27 : Bnd ((((((((Real.exp (-((9 : ℝ) / 16000))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((27 : ℝ) / 16000)))) + (Real.exp (-((171 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((81 : ℝ) / 8000))))) (6.9742359981908830968843479 : ℝ) (6.9742359981908830968843485 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 : Bnd (-((9 : ℝ) / 16000)) (-((9 : ℝ) / 16000)) (-((9 : ℝ) / 16000)) := Bnd.const _
  have h29 : Bnd ((Real.exp (-((9 : ℝ) / 16000)))) (9.9943765817346608496472466e-1 : ℝ) (9.9943765817346608496472467e-1 : ℝ) := Bnd.exp h28 (exp_ge' (-((9 : ℝ) / 16000)) (((9 : ℝ) / 16000)) (9.9943765817346608496472466e-1 : ℝ) 8 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-((9 : ℝ) / 16000)) (((9 : ℝ) / 16000)) (9.9943765817346608496472467e-1 : ℝ) 8 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h30 := Bnd.add h27 h29
  have h31 : Bnd (((((((((Real.exp (-((9 : ℝ) / 16000))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((27 : ℝ) / 16000)))) + (Real.exp (-((171 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((81 : ℝ) / 8000)))) + (Real.exp (-((9 : ℝ) / 16000))))) (7.9736736563643491818490725 : ℝ) (7.9736736563643491818490732 : ℝ) := h30.weak (by norm_num) (by norm_num)
  have h32 : Bnd (-((153 : ℝ) / 16000)) (-((153 : ℝ) / 16000)) (-((153 : ℝ) / 16000)) := Bnd.const _
  have h33 : Bnd ((Real.exp (-((153 : ℝ) / 16000)))) (9.9048307531611565576790577e-1 : ℝ) (9.9048307531611565576790578e-1 : ℝ) := Bnd.exp h32 (exp_ge' (-((153 : ℝ) / 16000)) (((153 : ℝ) / 16000)) (9.9048307531611565576790577e-1 : ℝ) 12 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-((153 : ℝ) / 16000)) (((153 : ℝ) / 16000)) (9.9048307531611565576790578e-1 : ℝ) 12 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h34 := Bnd.add h31 h33
  have h35 : Bnd ((((((((((Real.exp (-((9 : ℝ) / 16000))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((27 : ℝ) / 16000)))) + (Real.exp (-((171 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((81 : ℝ) / 8000)))) + (Real.exp (-((9 : ℝ) / 16000)))) + (Real.exp (-((153 : ℝ) / 16000))))) (8.9641567316804648376169782 : ℝ) (8.964156731680464837616979 : ℝ) := h34.weak (by norm_num) (by norm_num)
  have h36 : Bnd (-((9 : ℝ) / 1000)) (-((9 : ℝ) / 1000)) (-((9 : ℝ) / 1000)) := Bnd.const _
  have h37 : Bnd ((Real.exp (-((9 : ℝ) / 1000)))) (9.9104037877288366216456477e-1 : ℝ) (9.9104037877288366216456478e-1 : ℝ) := Bnd.exp h36 (exp_ge' (-((9 : ℝ) / 1000)) (((9 : ℝ) / 1000)) (9.9104037877288366216456477e-1 : ℝ) 12 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' (-((9 : ℝ) / 1000)) (((9 : ℝ) / 1000)) (9.9104037877288366216456478e-1 : ℝ) 12 (by norm_num) (by norm_num [abs_of_neg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h38 := Bnd.add h35 h37
  have h39 : Bnd (((((((((((Real.exp (-((9 : ℝ) / 16000))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((27 : ℝ) / 16000)))) + (Real.exp (-((171 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((81 : ℝ) / 8000)))) + (Real.exp (-((9 : ℝ) / 16000)))) + (Real.exp (-((153 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 1000))))) (9.9551971104533484997815429 : ℝ) (9.9551971104533484997815438 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.mul h1 h39 (by norm_num) (by norm_num)
  have h41 : Bnd ((((1 : ℝ) / 10) * ((((((((((Real.exp (-((9 : ℝ) / 16000))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((27 : ℝ) / 16000)))) + (Real.exp (-((171 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 8000)))) + (Real.exp (-((81 : ℝ) / 8000)))) + (Real.exp (-((9 : ℝ) / 16000)))) + (Real.exp (-((153 : ℝ) / 16000)))) + (Real.exp (-((9 : ℝ) / 1000)))))) (9.9551971104533484997815429e-1 : ℝ) (9.9551971104533484997815438e-1 : ℝ) := h40.weak (by norm_num) (by norm_num)
  exact h41

/-- The clock at the tilt `-ν`: `M_Q(-ν) = (1/10) Σ_D e^{νD}`. -/
noncomputable def qMQm : ℝ :=
  (((1 : ℝ) / 10) * ((((((((((Real.exp ((9 : ℝ) / 16000)) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((27 : ℝ) / 16000))) + (Real.exp ((171 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((81 : ℝ) / 8000))) + (Real.exp ((9 : ℝ) / 16000))) + (Real.exp ((153 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 1000))))

theorem qMQm_bnd : Bnd qMQm (1.0045198400566696603114352 : ℝ) (1.0045198400566696603114354 : ℝ) := by
  unfold qMQm
  have h1 : Bnd ((1 : ℝ) / 10) ((1 : ℝ) / 10) ((1 : ℝ) / 10) := Bnd.const _
  have h2 : Bnd ((9 : ℝ) / 16000) ((9 : ℝ) / 16000) ((9 : ℝ) / 16000) := Bnd.const _
  have h3 : Bnd ((Real.exp ((9 : ℝ) / 16000))) (1.0005626582327922577782832 : ℝ) (1.0005626582327922577782833 : ℝ) := Bnd.exp h2 (exp_ge' ((9 : ℝ) / 16000) (((9 : ℝ) / 16000)) (1.0005626582327922577782832 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' ((9 : ℝ) / 16000) (((9 : ℝ) / 16000)) (1.0005626582327922577782833 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h4 : Bnd ((9 : ℝ) / 8000) ((9 : ℝ) / 8000) ((9 : ℝ) / 8000) := Bnd.const _
  have h5 : Bnd ((Real.exp ((9 : ℝ) / 8000))) (1.0011256330498714444631127 : ℝ) (1.0011256330498714444631128 : ℝ) := Bnd.exp h4 (exp_ge' ((9 : ℝ) / 8000) (((9 : ℝ) / 8000)) (1.0011256330498714444631127 : ℝ) 9 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' ((9 : ℝ) / 8000) (((9 : ℝ) / 8000)) (1.0011256330498714444631128 : ℝ) 9 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h6 := Bnd.add h3 h5
  have h7 : Bnd (((Real.exp ((9 : ℝ) / 16000)) + (Real.exp ((9 : ℝ) / 8000)))) (2.0016882912826637022413959 : ℝ) (2.0016882912826637022413961 : ℝ) := h6.weak (by norm_num) (by norm_num)
  have h8 : Bnd ((27 : ℝ) / 16000) ((27 : ℝ) / 16000) ((27 : ℝ) / 16000) := Bnd.const _
  have h9 : Bnd ((Real.exp ((27 : ℝ) / 16000))) (1.0016889246293663154677041 : ℝ) (1.0016889246293663154677042 : ℝ) := Bnd.exp h8 (exp_ge' ((27 : ℝ) / 16000) (((27 : ℝ) / 16000)) (1.0016889246293663154677041 : ℝ) 10 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' ((27 : ℝ) / 16000) (((27 : ℝ) / 16000)) (1.0016889246293663154677042 : ℝ) 10 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h10 := Bnd.add h7 h9
  have h11 : Bnd ((((Real.exp ((9 : ℝ) / 16000)) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((27 : ℝ) / 16000)))) (3.0033772159120300177091 : ℝ) (3.0033772159120300177091003 : ℝ) := h10.weak (by norm_num) (by norm_num)
  have h12 : Bnd ((171 : ℝ) / 16000) ((171 : ℝ) / 16000) ((171 : ℝ) / 16000) := Bnd.const _
  have h13 : Bnd ((Real.exp ((171 : ℝ) / 16000))) (1.0107448153320128002696287 : ℝ) (1.0107448153320128002696288 : ℝ) := Bnd.exp h12 (exp_ge' ((171 : ℝ) / 16000) (((171 : ℝ) / 16000)) (1.0107448153320128002696287 : ℝ) 12 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' ((171 : ℝ) / 16000) (((171 : ℝ) / 16000)) (1.0107448153320128002696288 : ℝ) 12 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h14 := Bnd.add h11 h13
  have h15 : Bnd (((((Real.exp ((9 : ℝ) / 16000)) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((27 : ℝ) / 16000))) + (Real.exp ((171 : ℝ) / 16000)))) (4.0141220312440428179787287 : ℝ) (4.0141220312440428179787291 : ℝ) := h14.weak (by norm_num) (by norm_num)
  have h16 : Bnd ((9 : ℝ) / 16000) ((9 : ℝ) / 16000) ((9 : ℝ) / 16000) := Bnd.const _
  have h17 : Bnd ((Real.exp ((9 : ℝ) / 16000))) (1.0005626582327922577782832 : ℝ) (1.0005626582327922577782833 : ℝ) := Bnd.exp h16 (exp_ge' ((9 : ℝ) / 16000) (((9 : ℝ) / 16000)) (1.0005626582327922577782832 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' ((9 : ℝ) / 16000) (((9 : ℝ) / 16000)) (1.0005626582327922577782833 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h18 := Bnd.add h15 h17
  have h19 : Bnd ((((((Real.exp ((9 : ℝ) / 16000)) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((27 : ℝ) / 16000))) + (Real.exp ((171 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 16000)))) (5.0146846894768350757570119 : ℝ) (5.0146846894768350757570124 : ℝ) := h18.weak (by norm_num) (by norm_num)
  have h20 : Bnd ((9 : ℝ) / 8000) ((9 : ℝ) / 8000) ((9 : ℝ) / 8000) := Bnd.const _
  have h21 : Bnd ((Real.exp ((9 : ℝ) / 8000))) (1.0011256330498714444631127 : ℝ) (1.0011256330498714444631128 : ℝ) := Bnd.exp h20 (exp_ge' ((9 : ℝ) / 8000) (((9 : ℝ) / 8000)) (1.0011256330498714444631127 : ℝ) 9 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' ((9 : ℝ) / 8000) (((9 : ℝ) / 8000)) (1.0011256330498714444631128 : ℝ) 9 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h22 := Bnd.add h19 h21
  have h23 : Bnd (((((((Real.exp ((9 : ℝ) / 16000)) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((27 : ℝ) / 16000))) + (Real.exp ((171 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 8000)))) (6.0158103225267065202201246 : ℝ) (6.0158103225267065202201252 : ℝ) := h22.weak (by norm_num) (by norm_num)
  have h24 : Bnd ((81 : ℝ) / 8000) ((81 : ℝ) / 8000) ((81 : ℝ) / 8000) := Bnd.const _
  have h25 : Bnd ((Real.exp ((81 : ℝ) / 8000))) (1.0101764312463993115415373 : ℝ) (1.0101764312463993115415374 : ℝ) := Bnd.exp h24 (exp_ge' ((81 : ℝ) / 8000) (((81 : ℝ) / 8000)) (1.0101764312463993115415373 : ℝ) 12 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' ((81 : ℝ) / 8000) (((81 : ℝ) / 8000)) (1.0101764312463993115415374 : ℝ) 12 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h26 := Bnd.add h23 h25
  have h27 : Bnd ((((((((Real.exp ((9 : ℝ) / 16000)) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((27 : ℝ) / 16000))) + (Real.exp ((171 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((81 : ℝ) / 8000)))) (7.0259867537731058317616619 : ℝ) (7.0259867537731058317616626 : ℝ) := h26.weak (by norm_num) (by norm_num)
  have h28 : Bnd ((9 : ℝ) / 16000) ((9 : ℝ) / 16000) ((9 : ℝ) / 16000) := Bnd.const _
  have h29 : Bnd ((Real.exp ((9 : ℝ) / 16000))) (1.0005626582327922577782832 : ℝ) (1.0005626582327922577782833 : ℝ) := Bnd.exp h28 (exp_ge' ((9 : ℝ) / 16000) (((9 : ℝ) / 16000)) (1.0005626582327922577782832 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' ((9 : ℝ) / 16000) (((9 : ℝ) / 16000)) (1.0005626582327922577782833 : ℝ) 8 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h30 := Bnd.add h27 h29
  have h31 : Bnd (((((((((Real.exp ((9 : ℝ) / 16000)) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((27 : ℝ) / 16000))) + (Real.exp ((171 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((81 : ℝ) / 8000))) + (Real.exp ((9 : ℝ) / 16000)))) (8.0265494120058980895399451 : ℝ) (8.0265494120058980895399459 : ℝ) := h30.weak (by norm_num) (by norm_num)
  have h32 : Bnd ((153 : ℝ) / 16000) ((153 : ℝ) / 16000) ((153 : ℝ) / 16000) := Bnd.const _
  have h33 : Bnd ((Real.exp ((153 : ℝ) / 16000))) (1.0096083667869306995118367 : ℝ) (1.0096083667869306995118368 : ℝ) := Bnd.exp h32 (exp_ge' ((153 : ℝ) / 16000) (((153 : ℝ) / 16000)) (1.0096083667869306995118367 : ℝ) 12 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' ((153 : ℝ) / 16000) (((153 : ℝ) / 16000)) (1.0096083667869306995118368 : ℝ) 12 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h34 := Bnd.add h31 h33
  have h35 : Bnd ((((((((((Real.exp ((9 : ℝ) / 16000)) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((27 : ℝ) / 16000))) + (Real.exp ((171 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((81 : ℝ) / 8000))) + (Real.exp ((9 : ℝ) / 16000))) + (Real.exp ((153 : ℝ) / 16000)))) (9.0361577787928287890517818 : ℝ) (9.0361577787928287890517827 : ℝ) := h34.weak (by norm_num) (by norm_num)
  have h36 : Bnd ((9 : ℝ) / 1000) ((9 : ℝ) / 1000) ((9 : ℝ) / 1000) := Bnd.const _
  have h37 : Bnd ((Real.exp ((9 : ℝ) / 1000))) (1.0090406217738678140625704 : ℝ) (1.0090406217738678140625705 : ℝ) := Bnd.exp h36 (exp_ge' ((9 : ℝ) / 1000) (((9 : ℝ) / 1000)) (1.0090406217738678140625704 : ℝ) 12 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial])) (exp_le' ((9 : ℝ) / 1000) (((9 : ℝ) / 1000)) (1.0090406217738678140625705 : ℝ) 12 (by norm_num) (by norm_num [abs_of_nonneg]) (by norm_num) (by norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]))
  have h38 := Bnd.add h35 h37
  have h39 : Bnd (((((((((((Real.exp ((9 : ℝ) / 16000)) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((27 : ℝ) / 16000))) + (Real.exp ((171 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((81 : ℝ) / 8000))) + (Real.exp ((9 : ℝ) / 16000))) + (Real.exp ((153 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 1000)))) (1.0045198400566696603114352e1 : ℝ) (1.0045198400566696603114354e1 : ℝ) := h38.weak (by norm_num) (by norm_num)
  have h40 := Bnd.mul h1 h39 (by norm_num) (by norm_num)
  have h41 : Bnd ((((1 : ℝ) / 10) * ((((((((((Real.exp ((9 : ℝ) / 16000)) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((27 : ℝ) / 16000))) + (Real.exp ((171 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 8000))) + (Real.exp ((81 : ℝ) / 8000))) + (Real.exp ((9 : ℝ) / 16000))) + (Real.exp ((153 : ℝ) / 16000))) + (Real.exp ((9 : ℝ) / 1000))))) (1.0045198400566696603114352 : ℝ) (1.0045198400566696603114354 : ℝ) := h40.weak (by norm_num) (by norm_num)
  exact h41

/-- **The clock's overlap** `h = [M_Q(ν) M_Q(-ν)]^{-3/2}`. -/
noncomputable def qH : ℝ :=
  ((qMQp * qMQm) ^ (-(3 / 2 : ℝ)))

theorem qH_bnd : Bnd qH (9.9997104932968642721514519e-1 : ℝ) (9.999710493296864272151458e-1 : ℝ) := by
  unfold qH
  have h1 := Bnd.mul qMQp_bnd qMQm_bnd (by norm_num) (by norm_num)
  have h2 : Bnd ((qMQp * qMQm)) (1.0000193009125217601047568 : ℝ) (1.0000193009125217601047571 : ℝ) := h1.weak (by norm_num) (by norm_num)
  have h3 : Bnd (((qMQp * qMQm) ^ (-(3 / 2 : ℝ)))) ((1.000028951508479149845329 : ℝ))⁻¹ ((1.0000289515084791498453284 : ℝ))⁻¹ := Bnd.rpow_neg' (p := 3) (q := 2) h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 : Bnd (((qMQp * qMQm) ^ (-(3 / 2 : ℝ)))) (9.9997104932968642721514519e-1 : ℝ) (9.999710493296864272151458e-1 : ℝ) := h3.weak (by norm_num) (by norm_num)
  exact h4

end Comparison.Article
