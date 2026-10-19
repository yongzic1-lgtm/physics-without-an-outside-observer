import Comparison.WholePicture.Circulation

/-!
# The variance `‖θ_cyc‖²/24` of the phase insertion, and the `48`

Phases `θ` on the forty links of the sixteen vertices, oriented from `U` to
`V`. A step of a line from the vertex `x` along `s` traverses the link joining `x` and `transition s x` with
the phase `δ_s(x)`; the state `(x, t)` arrived along the link from `transition t x`, with the incoming phase
`a(x, t) = −δ_t(x)`.

* `phase_transition`: `δ_s(x) = ± θ_ℓ` on the one link `ℓ` joining `x` and `transition s x` (`coeff_table`, checked
  on all `16 · 5 · 40` cases); `sum_delta`: `Σ_s δ_s(x) = −div θ (x)`; `delta_sq_sum`: every link is met
  from both its ends, `Σ_x Σ_s δ_s(x)² = 2‖θ‖²`.
* `phase_poisson`: for a divergence-free `θ`, **`E[δ | (x, t)] = a(x, t)/4`** (`Σ_{s≠t} δ_s = a`), and the
  incoming phase of the next state is the traversed phase; so `b = a/3` solves the Poisson equation and
  the martingale increment is `(4δ − a)/3`.
* `phase_variance`: **`(1/320) Σ_arcs ((4δ − a)/3)² = ‖θ‖²/24`** for every divergence-free `θ`
  (in particular for `θ_cyc`, `WholePicture.divR_thetaCyc`): the variance per step is `‖θ_cyc‖²/24`,
  and the root moves by half of it, `log 4u_c = ‖θ_cyc‖²/48 + O(θ⁴)` (`WholePicture.long_range_zero`).
* `common_denominator`: `48 = 3 · 16 = 16(5 − 2) = 2(40 − 16)`; `regular_variance_algebra`: on a
  `d`-regular graph with `n` vertices the same moments give `σ² = 2‖ψ‖²/(n(d − 2))`.
-/

namespace Comparison.GroupsContinuumLaw

open WholePicture

/-- The link joining `x` and `transition s x`. -/
def linkTab : Fin 16 → Fin 5 → Fin 40 :=
  ![![0, 1, 2, 3, 4], ![0, 5, 6, 7, 8], ![9, 1, 10, 11, 12], ![13, 14, 2, 15, 16],
    ![17, 18, 19, 3, 20], ![21, 22, 23, 24, 4], ![9, 5, 27, 26, 25], ![13, 30, 6, 29, 28],
    ![17, 33, 32, 7, 31], ![21, 36, 35, 34, 8], ![37, 14, 10, 34, 31], ![38, 18, 35, 11, 28],
    ![39, 22, 32, 29, 12], ![39, 36, 19, 15, 25], ![38, 33, 23, 26, 16], ![37, 30, 27, 24, 20]]

/-- `+1` when the step leaves `x` at the link's tail `U`, `−1` at its head `V`. -/
def sgnTab : Fin 16 → Fin 5 → ℤ :=
  ![![1, 1, 1, 1, 1], ![-1, 1, 1, 1, 1], ![1, -1, 1, 1, 1], ![1, 1, -1, 1, 1],
    ![1, 1, 1, -1, 1], ![1, 1, 1, 1, -1], ![-1, -1, 1, 1, 1], ![-1, 1, -1, 1, 1],
    ![-1, 1, 1, -1, 1], ![-1, 1, 1, 1, -1], ![1, -1, -1, -1, -1], ![1, -1, -1, -1, -1],
    ![1, -1, -1, -1, -1], ![-1, -1, -1, -1, -1], ![-1, -1, -1, -1, -1], ![-1, -1, -1, -1, -1]]

/-- The coefficient of `θ_ℓ` in the phase of the passage `x → y`. -/
def coeff (l : Fin 40) (y x : Fin 16) : ℤ :=
  (if x = linkU l ∧ y = linkV l then 1 else 0) - (if x = linkV l ∧ y = linkU l then 1 else 0)

/-- The phase of the passage `x → y`. -/
noncomputable def phase16 (θ : Fin 40 → ℝ) (y x : Fin 16) : ℝ := ∑ l, θ l * (coeff l y x : ℝ)

theorem coeff_table : ∀ (x : Fin 16) (s : Fin 5) (l : Fin 40),
    coeff l (transition s x) x = if l = linkTab x s then sgnTab x s else 0 := by
  decide +kernel

theorem coeff_antisymm : ∀ (l : Fin 40) (x y : Fin 16), coeff l x y = -coeff l y x := by
  decide +kernel

theorem sgn_sq : ∀ (x : Fin 16) (s : Fin 5), sgnTab x s * sgnTab x s = 1 := by decide

theorem fibre_two : ∀ l : Fin 40,
    (Finset.univ.filter fun p : Fin 16 × Fin 5 => linkTab p.1 p.2 = l).card = 2 := by
  decide +kernel

theorem incZ_table : ∀ (x : Fin 16) (l : Fin 40),
    incZ x l = -∑ s, (if linkTab x s = l then sgnTab x s else 0) := by
  decide +kernel

/-- **One step traverses one link:** `δ_s(x) = sgn · θ_ℓ`. -/
theorem phase_transition (θ : Fin 40 → ℝ) (x : Fin 16) (s : Fin 5) :
    phase16 θ (transition s x) x = (sgnTab x s : ℝ) * θ (linkTab x s) := by
  rw [phase16]
  simp only [coeff_table]
  rw [Finset.sum_eq_single (linkTab x s)]
  · simp only [if_true]
    ring
  · intro b _ hb
    simp [hb]
  · simp

theorem phase_antisymm (θ : Fin 40 → ℝ) (x y : Fin 16) : phase16 θ x y = -phase16 θ y x := by
  rw [phase16, phase16, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coeff_antisymm l x y]
  push_cast
  ring

/-- **The five steps from a vertex carry minus its divergence:** `Σ_s δ_s(x) = −div θ (x)`. -/
theorem sum_delta (θ : Fin 40 → ℝ) (x : Fin 16) :
    ∑ s, phase16 θ (transition s x) x = -divR θ x := by
  simp only [phase_transition, divR, incZ_table]
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib, neg_neg, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single (linkTab x s)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- **Every link is met from both its ends:** `Σ_x Σ_s δ_s(x)² = 2‖θ‖²`. -/
theorem delta_sq_sum (θ : Fin 40 → ℝ) :
    ∑ x, ∑ s, phase16 θ (transition s x) x ^ 2 = 2 * sqL θ := by
  have hsq : ∀ x s, phase16 θ (transition s x) x ^ 2 = θ (linkTab x s) ^ 2 := by
    intro x s
    rw [phase_transition]
    have := sgn_sq x s
    have h : ((sgnTab x s : ℝ)) ^ 2 = 1 := by
      rw [sq]
      exact_mod_cast this
    calc ((sgnTab x s : ℝ) * θ (linkTab x s)) ^ 2 = (sgnTab x s : ℝ) ^ 2 * θ (linkTab x s) ^ 2 := by
          ring
      _ = θ (linkTab x s) ^ 2 := by rw [h, one_mul]
  simp only [hsq]
  rw [← Fintype.sum_prod_type' (fun x s => θ (linkTab x s) ^ 2)]
  rw [← Finset.sum_fiberwise Finset.univ (fun p : Fin 16 × Fin 5 => linkTab p.1 p.2)
    (fun p => θ (linkTab p.1 p.2) ^ 2)]
  rw [sqL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => θ l ^ 2) (fun p hp => by
    rw [(Finset.mem_filter.mp hp).2])]
  rw [Finset.sum_const, fibre_two, nsmul_eq_mul]
  norm_num

/-- **The conditional mean and the traversed phase:** for a divergence-free `θ`,
`Σ_{s≠t} δ_s(x) = a(x, t)` (so `E[δ | (x,t)] = a/4`) and `a(transition s x, s) = δ_s(x)`. -/
theorem phase_poisson (θ : Fin 40 → ℝ) (hdiv : ∀ x, divR θ x = 0) :
    (∀ x t, ∑ s, (if s = t then 0 else phase16 θ (transition s x) x) = phase16 θ x (transition t x)) ∧
      (∀ x s, phase16 θ (transition s x) (transition s (transition s x)) = phase16 θ (transition s x) x) := by
  constructor
  · intro x t
    have h := sum_delta θ x
    rw [hdiv x, neg_zero] at h
    have e : ∑ s, (if s = t then 0 else phase16 θ (transition s x) x) =
        ∑ s, phase16 θ (transition s x) x - phase16 θ (transition t x) x := by
      have hs : ∀ s, (if s = t then (0 : ℝ) else phase16 θ (transition s x) x) =
          phase16 θ (transition s x) x - (if s = t then phase16 θ (transition t x) x else 0) := by
        intro s
        split_ifs with hst
        · rw [hst]
          ring
        · ring
      simp only [hs, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [e, h, phase_antisymm θ x (transition t x)]
    ring
  · intro x s
    rw [transition_transition]

/-- The identity behind the variance at one vertex: for five numbers summing to zero,
`Σ_{s≠t} (4δ_s + δ_t)² = 60 Σ δ²`. -/
theorem place_identity (d : Fin 5 → ℝ) (hd : ∑ s, d s = 0) :
    ∑ t, ∑ s, (if s = t then 0 else (4 * d s + d t) ^ 2) = 60 * ∑ s, d s ^ 2 := by
  have h4 : d 4 = -(d 0 + d 1 + d 2 + d 3) := by
    rw [Fin.sum_univ_five] at hd
    linarith
  simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte, h4]
  ring

/-- **The variance of the phase insertion:** for every divergence-free `θ` (so for `θ_cyc`),
`(1/320) Σ_{arcs} ((4δ − a)/3)² = ‖θ‖²/24`. -/
theorem phase_variance (θ : Fin 40 → ℝ) (hdiv : ∀ x, divR θ x = 0) :
    (∑ x, ∑ t, ∑ s, (if s = t then 0 else
        ((4 * phase16 θ (transition s x) x - phase16 θ x (transition t x)) / 3) ^ 2)) / 320 =
      sqL θ / 24 := by
  have hx : ∀ x, ∑ t, ∑ s, (if s = t then 0 else
      ((4 * phase16 θ (transition s x) x - phase16 θ x (transition t x)) / 3) ^ 2) =
      60 / 9 * ∑ s, phase16 θ (transition s x) x ^ 2 := by
    intro x
    have hd : ∑ s, phase16 θ (transition s x) x = 0 := by rw [sum_delta, hdiv x, neg_zero]
    have e : ∀ s t, ((4 * phase16 θ (transition s x) x - phase16 θ x (transition t x)) / 3) ^ 2 =
        (4 * phase16 θ (transition s x) x + phase16 θ (transition t x) x) ^ 2 / 9 := by
      intro s t
      rw [phase_antisymm θ x (transition t x)]
      ring
    simp only [e]
    have := place_identity (fun s => phase16 θ (transition s x) x) hd
    have e2 : ∀ t, ∑ s, (if s = t then (0 : ℝ) else
        (4 * phase16 θ (transition s x) x + phase16 θ (transition t x) x) ^ 2 / 9) =
        (∑ s, (if s = t then (0 : ℝ) else
          (4 * phase16 θ (transition s x) x + phase16 θ (transition t x) x) ^ 2)) / 9 := by
      intro t
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> simp
    simp only [e2, ← Finset.sum_div, this]
    ring
  simp only [hx, ← Finset.mul_sum, delta_sq_sum]
  ring

/-- **The variance of `θ_cyc`:** the cyclic part of any phases has the variance `‖θ_cyc‖²/24`. -/
theorem cyc_variance (θ : Fin 40 → ℝ) :
    (∑ x, ∑ t, ∑ s, (if s = t then 0 else
        ((4 * phase16 (thetaCyc θ) (transition s x) x - phase16 (thetaCyc θ) x (transition t x)) / 3) ^ 2)) / 320 =
      sqL (thetaCyc θ) / 24 :=
  phase_variance (thetaCyc θ) (divR_thetaCyc θ)

/-- **The common denominator:** `48 = 3 · 16 = 16(5 − 2) = 2(40 − 16)`; the cycle rank is `25`. -/
theorem common_denominator :
    (3 : ℕ) * 16 = 16 * (5 - 2) ∧ (3 : ℕ) * 16 = 2 * (40 - 16) ∧ (3 : ℕ) * 16 = 48 ∧
      (40 : ℕ) - 16 + 1 = 25 ∧ (2 : ℚ) * (1 / 48) = 1 / 24 := by
  norm_num

/-- **On a `d`-regular graph:** the moments `Eδ² = Ea² = 2Q/(nd)`, `E(aδ) = Ea²/(d − 1)` give
`σ² = ((d−1)²Eδ² − 2(d−1)E(aδ) + Ea²)/(d − 2)² = 2Q/(n(d − 2))`. -/
theorem regular_variance_algebra (n d Q : ℝ) (hn : n ≠ 0) (hd : 2 < d) :
    (((d - 1) ^ 2 + 1) * (2 * Q / (n * d)) - 2 * (d - 1) * (2 * Q / (n * d * (d - 1)))) /
        (d - 2) ^ 2 = 2 * Q / (n * (d - 2)) := by
  have h1 : d - 1 ≠ 0 := by linarith
  have h2 : d - 2 ≠ 0 := by linarith
  have h0 : d ≠ 0 := by linarith
  field_simp
  ring

end Comparison.GroupsContinuumLaw
