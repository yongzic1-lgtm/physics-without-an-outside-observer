import Comparison.Colour.ClosedAvailableTransitions

/-!
# The logarithmic vertex, its restriction to the seventy-four, and `W = det(qI₃) = q³`

With the walk `P = B/4` (rows destinations), the available transitions of a last-step direction
`h` (the seventy-four states `A`, the six closed states `D`) and the available transitions density
`d_h = σ E_h + η (1 − E_h)`, `σ = 75/74`, `η = 295/296`:

* `density_values`: `5·C_h/M = 75/74` on the last-step direction, `5·59/M = 295/296` on each other line, sum `5`.
* `marked_entry`, `no_undo_on_mark`: the marked step `A_h = E_h P R_h` is `P ∘ H_h`, and `A_h E_h = 0`:
  a marked step arrives along `h`, so it comes from another remembered last-step direction.
* `incoming_outgoing_vertices`: **`V_in = (log t)P + A_h log 𝒟_h = P ∘ [log t + H_h log η]`** and
  `V_out = (log t)P + (log 𝒟_h)A_h = P ∘ [log t + H_h log σ]`; `vertex_rates`: their rates are
  `log t + (3/16) log η` and `log t + (3/16) log σ`; `preparations_differ`: `W_out/W_in = (60/59)⁹`.
* The restriction to the seventy-four (`S(z) = I − zP_AA − z²P_AD P_DA − z³P_AD P_DD P_DA`):
  `hidden_square_zero`: `P_DD² = 0`; `constant_lifts`: `R 𝟏_A = 𝟏`, `𝟏_A L = 𝟏`;
  `reduced_clock`: **`ℓ_A S_z r_A = −40/37`**; `reduced_source`: for every arc source `V`,
  `ℓ_A(−L V R) r_A = −ΣV/74`, and the ratio to the clock is `ΣV/80`; `marked_numerator`: **`−15/74`**,
  `marked_ratio`: **`3/16`**; `reduced_residue`: the matrix `𝟏𝟏ᵀ/80` satisfies `S(1)M = M S(1) = 0`
  and equals `−r ℓ/(ℓ S_z r)`: **the residue `1/80`**.
* `colour_word`, `W_three_excursions`: **`det(q I₃) = q³`** and `q = t¹⁶η³` gives `W = t⁴⁸η⁹`.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix Real

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

/-! ## The available transitions density and the marked step -/

/-- The available transitions density on the remembered last-step direction `s`: `5 · (continuations along s)/M`. -/
noncomputable def densityQ (h s : Fin 5) : ℚ := 5 * (alongCount h s : ℚ) / 296

/-- **The available transitions density:** `75/74` on the last-step direction, `295/296` on each other line, summing to five. -/
theorem density_values (h : Fin 5) :
    densityQ h h = 75 / 74 ∧ (∀ s, s ≠ h → densityQ h s = 295 / 296) ∧ ∑ s, densityQ h s = 5 := by
  have h1 := (availableTransitions_along h).1
  have h2 := (availableTransitions_along h).2
  have ht := availableTransitions_total h
  refine ⟨?_, fun s hs => ?_, ?_⟩
  · rw [densityQ, h1]
    norm_num
  · rw [densityQ, h2 s hs]
    norm_num
  · simp only [densityQ]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have : (∑ s, (alongCount h s : ℚ)) = 296 := by exact_mod_cast ht
    rw [this]
    norm_num

/-- The walk over `ℝ`, rows destinations. -/
noncomputable def lawR : Matrix State State ℝ := fun p q => if Continues q p then 1 / 4 else 0

/-- The projector on the states whose remembered last-step direction is `h`. -/
noncomputable def lastDirectionProj (h : Fin 5) : Matrix State State ℝ :=
  Matrix.diagonal fun s => if s.2 = h then 1 else 0

/-- The projector on the available transitions of `h`. -/
noncomputable def availableTransitionsProj (h : Fin 5) : Matrix State State ℝ :=
  Matrix.diagonal fun s => if InAvailableTransitions h s then 1 else 0

/-- **The marked step** `A_h = E_h P R_h`. -/
noncomputable def markedR (h : Fin 5) : Matrix State State ℝ := lastDirectionProj h * lawR * availableTransitionsProj h

theorem marked_entry (h : Fin 5) (i j : State) :
    markedR h i j = lawR i j * (if InAvailableTransitions h j ∧ i.2 = h then 1 else 0) := by
  simp only [markedR, lastDirectionProj, availableTransitionsProj, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i.2 = h <;> by_cases hj : InAvailableTransitions h j <;> simp [hi, hj]

theorem marked_zero_of_lastDirection (h : Fin 5) (i j : State) (hj : j.2 = h) : markedR h i j = 0 := by
  rw [marked_entry, lawR]
  by_cases hc : Continues j i
  · have hne : i.2 ≠ j.2 := hc.1
    have : ¬(InAvailableTransitions h j ∧ i.2 = h) := fun ⟨_, hi⟩ => hne (hi.trans hj.symm)
    simp [this]
  · simp [hc]

/-- **A marked step comes from another remembered last-step direction:** `A_h E_h = 0`, `E_h A_h = A_h`. -/
theorem no_undo_on_mark (h : Fin 5) :
    markedR h * lastDirectionProj h = 0 ∧ lastDirectionProj h * markedR h = markedR h := by
  constructor
  · ext i j
    rw [lastDirectionProj, Matrix.mul_diagonal, Matrix.zero_apply]
    by_cases hj : j.2 = h
    · rw [marked_zero_of_lastDirection h i j hj, zero_mul]
    · simp [hj]
  · ext i j
    rw [lastDirectionProj, Matrix.diagonal_mul, marked_entry]
    by_cases hi : i.2 = h <;> simp [hi]

/-- The logarithm of the available transitions density on the remembered last-step direction. -/
noncomputable def logDensity (h : Fin 5) : Matrix State State ℝ :=
  Matrix.diagonal fun s => Real.log (densityQ h s.2 : ℝ)

/-- The incoming preparation `V_in = (log t)P + A_h log 𝒟_h`. -/
noncomputable def vin (h : Fin 5) : Matrix State State ℝ :=
  Real.log (2 / 5) • lawR + markedR h * logDensity h

/-- The outgoing preparation `V_out = (log t)P + (log 𝒟_h) A_h`. -/
noncomputable def vout (h : Fin 5) : Matrix State State ℝ :=
  Real.log (2 / 5) • lawR + logDensity h * markedR h

/-- **The two preparations from the one available-transition density:** `V_in` vertices `η` and `V_out` vertices `σ`
on the sixty marked arcs. -/
theorem incoming_outgoing_vertices (h : Fin 5) :
    vin h = Real.log (2 / 5) • lawR + Real.log (295 / 296) • markedR h ∧
      vout h = Real.log (2 / 5) • lawR + Real.log (75 / 74) • markedR h := by
  obtain ⟨dh, dother, _⟩ := density_values h
  constructor
  · rw [vin]
    congr 1
    ext i j
    rw [logDensity, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    by_cases hj : j.2 = h
    · rw [marked_zero_of_lastDirection h i j hj]
      ring
    · rw [dother j.2 hj]
      push_cast
      ring
  · rw [vout]
    congr 1
    ext i j
    rw [logDensity, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    by_cases hi : i.2 = h
    · rw [hi, dh]
      push_cast
      ring
    · have : markedR h i j = 0 := by
        rw [marked_entry]
        simp [hi]
      rw [this]
      ring

/-- Entry form: `V_in = P ∘ [log t + H_h log η]`. -/
theorem incoming_vertex_entry (h : Fin 5) (i j : State) :
    vin h i j = lawR i j *
      (Real.log (2 / 5) + (if InAvailableTransitions h j ∧ i.2 = h then 1 else 0) * Real.log (295 / 296)) := by
  rw [(incoming_outgoing_vertices h).1, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    marked_entry, smul_eq_mul, smul_eq_mul]
  ring

theorem sum_boole_pairs (P : State → State → Prop) [DecidableRel P] :
    ∑ i, ∑ j, (if P i j then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun x : State × State => P x.1 x.2).card : ℝ) := by
  rw [← Fintype.sum_prod_type' (fun i j => if P i j then (1 : ℝ) else 0), Finset.sum_boole]

theorem card_marked : ∀ h : Fin 5,
    (Finset.univ.filter fun x : State × State =>
      Continues x.2 x.1 ∧ InAvailableTransitions h x.2 ∧ x.1.2 = h).card = 60 := by
  decide +kernel

theorem card_arcs_rows :
    (Finset.univ.filter fun x : State × State => Continues x.2 x.1).card = 320 := by
  decide +kernel

theorem sum_lawR : ∑ i, ∑ j, lawR i j = 80 := by
  have h := sum_boole_pairs (fun i j => Continues j i)
  rw [card_arcs_rows] at h
  have e : ∀ i j, lawR i j = (1 / 4) * (if Continues j i then (1 : ℝ) else 0) := by
    intro i j
    simp only [lawR]
    split_ifs <;> ring
  simp only [e, ← Finset.mul_sum, h]
  norm_num

theorem sum_marked (h : Fin 5) : ∑ i, ∑ j, markedR h i j = 15 := by
  have hc := sum_boole_pairs (fun i j => Continues j i ∧ InAvailableTransitions h j ∧ i.2 = h)
  rw [card_marked h] at hc
  have e : ∀ i j, markedR h i j =
      (1 / 4) * (if Continues j i ∧ InAvailableTransitions h j ∧ i.2 = h then (1 : ℝ) else 0) := by
    intro i j
    rw [marked_entry, lawR]
    by_cases h1 : Continues j i <;> by_cases h2 : InAvailableTransitions h j ∧ i.2 = h <;> simp [h1, h2]
  simp only [e, ← Finset.mul_sum, hc]
  norm_num

/-- **The rates of the two preparations:** `log t + (3/16) log η` and `log t + (3/16) log σ`. -/
theorem vertex_rates (h : Fin 5) :
    (∑ i, ∑ j, vin h i j) / 80 = Real.log (2 / 5) + 3 / 16 * Real.log (295 / 296) ∧
      (∑ i, ∑ j, vout h i j) / 80 = Real.log (2 / 5) + 3 / 16 * Real.log (75 / 74) := by
  obtain ⟨hi, ho⟩ := incoming_outgoing_vertices h
  have hl := sum_lawR
  have hm := sum_marked h
  constructor
  · rw [hi]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hl, hm]
    ring
  · rw [ho]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hl, hm]
    ring

/-- **The two preparations give different colour words:** `W_out/W_in = (60/59)⁹ > 1`, and their
rates differ by `(3/16) log(60/59) > 0`. -/
theorem preparations_differ :
    ((2 / 5 : ℚ) ^ 48 * (75 / 74) ^ 9) / ((2 / 5) ^ 48 * (295 / 296) ^ 9) = (60 / 59) ^ 9 ∧
      (2 / 5 : ℚ) ^ 48 * (295 / 296) ^ 9 < (2 / 5) ^ 48 * (75 / 74) ^ 9 ∧
      3 / 16 * Real.log (75 / 74) - 3 / 16 * Real.log (295 / 296) = 3 / 16 * Real.log (60 / 59) ∧
      0 < 3 / 16 * Real.log (60 / 59) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [← mul_sub, ← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  · have : 0 < Real.log (60 / 59) := Real.log_pos (by norm_num)
    positivity

/-! ## The restriction to the seventy-four -/

section Closing

variable (h : Fin 5)

/-- The available transitions as a type. -/
abbrev Ret := {s : State // InAvailableTransitions h s}

/-- The closed states as a type. -/
abbrev Hid := {s : State // ¬InAvailableTransitions h s}

/-- The blocks of `B`: rows destinations, columns sources. -/
abbrev bAA : Matrix (Ret h) (Ret h) ℚ := stepQ.toBlock (InAvailableTransitions h) (InAvailableTransitions h)
abbrev bAD : Matrix (Ret h) (Hid h) ℚ := stepQ.toBlock (InAvailableTransitions h) (fun s => ¬InAvailableTransitions h s)
abbrev bDA : Matrix (Hid h) (Ret h) ℚ := stepQ.toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h)
abbrev bDD : Matrix (Hid h) (Hid h) ℚ := blockDD h (fun _ _ => (1 : ℚ))

theorem card_Ret : Fintype.card (Ret h) = 74 := by
  rw [Fintype.card_subtype]
  exact card_excursionStates h

theorem card_Hid : Fintype.card (Hid h) = 6 := by
  rw [Fintype.card_subtype_compl, card_Ret, card_state]

theorem rowA : bAA h *ᵥ (1 : Ret h → ℚ) = (4 : ℚ) • 1 - bAD h *ᵥ 1 := by
  ext i
  have e := congrFun stepQ_mulVec_one i
  rw [mulVec_split stepQ (InAvailableTransitions h) (InAvailableTransitions h) i] at e
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at e ⊢
  linarith

theorem rowD : bDA h *ᵥ (1 : Ret h → ℚ) = (4 : ℚ) • 1 - bDD h *ᵥ 1 := by
  ext i
  have e := congrFun stepQ_mulVec_one i
  rw [mulVec_split stepQ (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h) i] at e
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at e ⊢
  linarith

theorem colA : (1 : Ret h → ℚ) ᵥ* bAA h = (4 : ℚ) • 1 - (1 : Hid h → ℚ) ᵥ* bDA h := by
  ext j
  have e := congrFun stepQ_vecMul_one j
  rw [vecMul_split stepQ (InAvailableTransitions h) (InAvailableTransitions h) j] at e
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at e ⊢
  linarith

theorem colD : (1 : Ret h → ℚ) ᵥ* bAD h = (4 : ℚ) • 1 - (1 : Hid h → ℚ) ᵥ* bDD h := by
  ext j
  have e := congrFun stepQ_vecMul_one j
  rw [vecMul_split stepQ (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h) j] at e
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at e ⊢
  linarith

/-- **The hidden step squares to zero:** `B_DD² = 0`. -/
theorem hidden_square_zero : bDD h * bDD h = 0 := blockDD_sq h _

theorem totDD_all : ∀ h : Fin 5,
    (1 : {s : State // ¬InAvailableTransitions h s} → ℚ) ⬝ᵥ (blockDD h (fun _ _ => (1 : ℚ)) *ᵥ 1) = 4 := by
  decide +kernel

theorem dot_one_one_Hid : (1 : Hid h → ℚ) ⬝ᵥ (1 : Hid h → ℚ) = 6 := by
  simp only [dotProduct, Pi.one_apply, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_Hid]
  norm_num

theorem dot_one_one_Ret : (1 : Ret h → ℚ) ⬝ᵥ (1 : Ret h → ℚ) = 74 := by
  simp only [dotProduct, Pi.one_apply, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_Ret]
  norm_num

theorem nilv (v : Hid h → ℚ) : bDD h *ᵥ (bDD h *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec, hidden_square_zero, Matrix.zero_mulVec]

theorem tot2 : (1 : Ret h → ℚ) ⬝ᵥ ((bAD h * bDA h) *ᵥ 1) = 64 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, rowD, colD]
  have hD := totDD_all h
  have hsym : ((1 : Hid h → ℚ) ᵥ* bDD h) ⬝ᵥ (1 : Hid h → ℚ) = 4 := by
    rw [← Matrix.dotProduct_mulVec]
    exact hD
  have hzero : ((1 : Hid h → ℚ) ᵥ* bDD h) ⬝ᵥ (bDD h *ᵥ 1) = 0 := by
    rw [← Matrix.dotProduct_mulVec, nilv, dotProduct_zero]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dot_one_one_Hid, hD, hsym, hzero]
  norm_num

theorem tot3 : (1 : Ret h → ℚ) ⬝ᵥ ((bAD h * bDD h * bDA h) *ᵥ 1) = 64 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, rowD, colD]
  have hD := totDD_all h
  have hz2 : ((1 : Hid h → ℚ) ᵥ* bDD h) ⬝ᵥ (bDD h *ᵥ 1) = 0 := by
    rw [← Matrix.dotProduct_mulVec, nilv, dotProduct_zero]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, nilv, sub_zero, sub_dotProduct,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, hD, hz2]
  norm_num

theorem tot1 : (1 : Ret h → ℚ) ⬝ᵥ (bAA h *ᵥ 1) = 276 := by
  rw [rowA]
  have h1 : (1 : Ret h → ℚ) ⬝ᵥ (bAD h *ᵥ 1) = 20 := by
    rw [Matrix.dotProduct_mulVec, colD]
    have hD := totDD_all h
    have hsym : ((1 : Hid h → ℚ) ᵥ* bDD h) ⬝ᵥ (1 : Hid h → ℚ) = 4 := by
      rw [← Matrix.dotProduct_mulVec]
      exact hD
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, dot_one_one_Hid, hsym]
    norm_num
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, dot_one_one_Ret, h1]
  norm_num

/-- The reduced operator `S(z) = I − zP_AA − z²P_AD P_DA − z³P_AD P_DD P_DA` (`P = B/4`). -/
noncomputable def Sred (z : ℚ) : Matrix (Ret h) (Ret h) ℚ :=
  1 - (z / 4) • bAA h - (z / 4) ^ 2 • (bAD h * bDA h) - (z / 4) ^ 3 • (bAD h * bDD h * bDA h)

/-- Its derivative at `z = 1`: `S_z = −(P_AA + 2P_AD P_DA + 3P_AD P_DD P_DA)`. -/
noncomputable def Sz : Matrix (Ret h) (Ret h) ℚ :=
  -((1 / 4 : ℚ) • bAA h + (2 / 16 : ℚ) • (bAD h * bDA h) + (3 / 64 : ℚ) • (bAD h * bDD h * bDA h))

/-- **The reduced clock:** `ℓ_A S_z r_A = −40/37` with `r_A = 𝟏`, `ℓ_A = 𝟏ᵀ/74`. -/
theorem reduced_clock : (1 / 74 : ℚ) * ((1 : Ret h → ℚ) ⬝ᵥ (Sz h *ᵥ 1)) = -40 / 37 := by
  have h1 := tot1 h
  have h2 := tot2 h
  have h3 := tot3 h
  simp only [Sz, Matrix.neg_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_neg,
    dotProduct_add, dotProduct_smul, smul_eq_mul, h1, h2, h3]
  norm_num

/-- The retained coordinates and the closed coordinates as maps into the eighty states. -/
def ea : Matrix State (Ret h) ℚ := fun s a => if s = a.val then 1 else 0
def ed : Matrix State (Hid h) ℚ := fun s d => if s = d.val then 1 else 0

/-- `R = (1; (1 + P_DD) P_DA)` at `z = 1`. -/
noncomputable def liftR : Matrix State (Ret h) ℚ :=
  ea h + ed h * (1 + (1 / 4 : ℚ) • bDD h) * ((1 / 4 : ℚ) • bDA h)

/-- `L = (1, P_AD (1 + P_DD))` at `z = 1`. -/
noncomputable def liftL : Matrix (Ret h) State ℚ :=
  (ea h)ᵀ + ((1 / 4 : ℚ) • bAD h) * (1 + (1 / 4 : ℚ) • bDD h) * (ed h)ᵀ

theorem ea_ed_one : ea h *ᵥ (1 : Ret h → ℚ) + ed h *ᵥ (1 : Hid h → ℚ) = 1 := by
  ext s
  simp only [ea, ed, Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, Pi.add_apply]
  by_cases hs : InAvailableTransitions h s
  · rw [Finset.sum_eq_single ⟨s, hs⟩, Finset.sum_eq_zero]
    · simp
    · intro d _
      have : s ≠ d.val := fun e => d.2 (e ▸ hs)
      simp [this]
    · intro b _ hb
      have : s ≠ b.val := fun e => hb (Subtype.ext e.symm)
      simp [this]
    · simp
  · rw [Finset.sum_eq_zero, Finset.sum_eq_single ⟨s, hs⟩]
    · simp
    · intro b _ hb
      have : s ≠ b.val := fun e => hb (Subtype.ext e.symm)
      simp [this]
    · simp
    · intro a _
      have : s ≠ a.val := fun e => hs (e ▸ a.2)
      simp [this]

theorem one_ea_ed : (1 : State → ℚ) ᵥ* ea h = 1 ∧ (1 : State → ℚ) ᵥ* ed h = 1 := by
  constructor
  · ext a
    simp only [ea, Matrix.vecMul, dotProduct, Pi.one_apply, one_mul]
    rw [Finset.sum_ite_eq']
    simp
  · ext d
    simp only [ed, Matrix.vecMul, dotProduct, Pi.one_apply, one_mul]
    rw [Finset.sum_ite_eq']
    simp

/-- **The constant lifts:** `R 𝟏_A = 𝟏` and `𝟏_A L = 𝟏`. -/
theorem constant_lifts :
    liftR h *ᵥ (1 : Ret h → ℚ) = 1 ∧ (1 : Ret h → ℚ) ᵥ* liftL h = 1 := by
  constructor
  · have hD : (1 + (1 / 4 : ℚ) • bDD h) *ᵥ (((1 / 4 : ℚ) • bDA h) *ᵥ (1 : Ret h → ℚ)) = 1 := by
      rw [Matrix.smul_mulVec, rowD, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      simp only [smul_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_smul, nilv, smul_zero]
      module
    rw [liftR, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hD, ea_ed_one]
  · have hD : ((1 : Ret h → ℚ) ᵥ* ((1 / 4 : ℚ) • bAD h)) ᵥ* (1 + (1 / 4 : ℚ) • bDD h) = 1 := by
      rw [Matrix.vecMul_smul, colD, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul]
      have hz : ((1 : Hid h → ℚ) ᵥ* bDD h) ᵥ* bDD h = 0 := by
        rw [Matrix.vecMul_vecMul, hidden_square_zero, Matrix.vecMul_zero]
      simp only [smul_sub, Matrix.sub_vecMul, Matrix.smul_vecMul, smul_smul, hz, smul_zero]
      module
    rw [liftL, Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hD,
      Matrix.vecMul_transpose, Matrix.vecMul_transpose, ea_ed_one]

/-- **Every arc source keeps its rate through the bound state:** for every source `V` on the eighty
states, `ℓ_A (−L V R) r_A = −ΣV/74`, and the ratio to the clock `ℓ_A S_z r_A` is `ΣV/80`. -/
theorem reduced_source (V : Matrix State State ℚ) :
    (1 / 74 : ℚ) * ((1 : Ret h → ℚ) ⬝ᵥ ((-(liftL h * V * liftR h)) *ᵥ 1)) =
        -((1 : State → ℚ) ⬝ᵥ (V *ᵥ 1)) / 74 ∧
      ((1 / 74 : ℚ) * ((1 : Ret h → ℚ) ⬝ᵥ ((-(liftL h * V * liftR h)) *ᵥ 1))) /
          ((1 / 74 : ℚ) * ((1 : Ret h → ℚ) ⬝ᵥ (Sz h *ᵥ 1))) =
        ((1 : State → ℚ) ⬝ᵥ (V *ᵥ 1)) / 80 := by
  obtain ⟨hR, hL⟩ := constant_lifts h
  have key : (1 : Ret h → ℚ) ⬝ᵥ ((liftL h * V * liftR h) *ᵥ 1) = (1 : State → ℚ) ⬝ᵥ (V *ᵥ 1) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hR, Matrix.dotProduct_mulVec, hL]
  have e : (1 / 74 : ℚ) * ((1 : Ret h → ℚ) ⬝ᵥ ((-(liftL h * V * liftR h)) *ᵥ 1)) =
      -((1 : State → ℚ) ⬝ᵥ (V *ᵥ 1)) / 74 := by
    rw [Matrix.neg_mulVec, dotProduct_neg, key]
    ring
  refine ⟨e, ?_⟩
  rw [e, reduced_clock]
  ring

/-- The marked step over `ℚ`. -/
def markedQ : Matrix State State ℚ :=
  fun i j => if Continues j i ∧ InAvailableTransitions h j ∧ i.2 = h then 1 / 4 else 0

theorem sum_markedQ : (1 : State → ℚ) ⬝ᵥ (markedQ h *ᵥ 1) = 15 := by
  have hc : ∑ i, ∑ j, (if Continues j i ∧ InAvailableTransitions h j ∧ i.2 = h then (1 : ℚ) else 0) = 60 := by
    rw [← Fintype.sum_prod_type' (fun i j => if Continues j i ∧ InAvailableTransitions h j ∧ i.2 = h then (1 : ℚ)
      else 0), Finset.sum_boole, card_marked h]
    norm_num
  simp only [dotProduct, Matrix.mulVec, Pi.one_apply, one_mul, mul_one, markedQ]
  have e : ∀ i j, (if Continues j i ∧ InAvailableTransitions h j ∧ i.2 = h then (1 / 4 : ℚ) else 0) =
      (1 / 4) * (if Continues j i ∧ InAvailableTransitions h j ∧ i.2 = h then (1 : ℚ) else 0) := by
    intro i j
    split_ifs <;> ring
  simp only [e, ← Finset.mul_sum, hc]
  norm_num

/-- **The marked numerator:** `ℓ_A(−L A_h R) r_A = −15/74`; **its ratio to the clock is `3/16`.** -/
theorem marked_numerator :
    (1 / 74 : ℚ) * ((1 : Ret h → ℚ) ⬝ᵥ ((-(liftL h * markedQ h * liftR h)) *ᵥ 1)) = -15 / 74 ∧
      ((1 / 74 : ℚ) * ((1 : Ret h → ℚ) ⬝ᵥ ((-(liftL h * markedQ h * liftR h)) *ᵥ 1))) /
          ((1 / 74 : ℚ) * ((1 : Ret h → ℚ) ⬝ᵥ (Sz h *ᵥ 1))) = 3 / 16 := by
  obtain ⟨e1, e2⟩ := reduced_source h (markedQ h)
  rw [sum_markedQ] at e1 e2
  refine ⟨by rw [e1], by rw [e2]; norm_num⟩

/-- **The clock's conversion:** a stationary excursion holds `74/5` watched steps and `16` original
steps, `(74/5)(40/37) = 16`, and `(15/74)/(40/37) = 3/16`. -/
theorem excursion_clock_transport : (74 / 5 : ℚ) * (40 / 37) = 16 ∧ (15 / 74 : ℚ) / (40 / 37) = 3 / 16 := by
  norm_num

/-- The watched walk is `I − S(1)`. -/
theorem Sred_one : Sred h 1 = 1 - watchedW h := by
  rw [Sred, watchedW]
  module

/-- The residue matrix `𝟏𝟏ᵀ/80` on the seventy-four. -/
def resM : Matrix (Ret h) (Ret h) ℚ := Matrix.of fun _ _ => 1 / 80

/-- **The residue `1/80`:** `M = 𝟏𝟏ᵀ/80` has `S(1)M = M S(1) = 0`, and `M = −r ℓ/(ℓ S_z r)` with
`r = 𝟏`, `ℓ = 𝟏ᵀ/74`. -/
theorem reduced_residue :
    Sred h 1 * resM h = 0 ∧ resM h * Sred h 1 = 0 ∧
      ∀ i j : Ret h, resM h i j =
        -(1 * (1 / 74)) / ((1 / 74 : ℚ) * ((1 : Ret h → ℚ) ⬝ᵥ (Sz h *ᵥ 1))) := by
  have hr := watched_rows h
  have hc := watched_cols h
  refine ⟨?_, ?_, fun _ _ => ?_⟩
  · ext i j
    rw [Sred_one, Matrix.mul_apply, Matrix.zero_apply]
    have := congrFun hr i
    simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one] at this
    simp only [resM, Matrix.of_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib,
      ← Finset.sum_mul, this]
    simp [Matrix.one_apply]
  · ext i j
    rw [Sred_one, Matrix.mul_apply, Matrix.zero_apply]
    have := congrFun hc j
    simp only [Matrix.vecMul, dotProduct, Pi.one_apply, one_mul] at this
    simp only [resM, Matrix.of_apply, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib,
      ← Finset.mul_sum, this]
    simp [Matrix.one_apply]
  · rw [reduced_clock, resM, Matrix.of_apply]
    norm_num

end Closing

/-! ## The three-colour word -/

/-- **The complete colour word is a determinant:** `det(q I₃) = q³`. -/
theorem colour_word (q : ℝ) : (Matrix.diagonal fun _ : Fin 3 => q).det = q ^ 3 := by
  rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The one-colour end and the three-colour word:** `q = t¹⁶η³` and `q³ = t⁴⁸η⁹`, `t = 2/5`,
`η = 295/296`. -/
theorem W_three_excursions :
    ((2 / 5 : ℝ) ^ 16 * (295 / 296) ^ 3) ^ 3 = (2 / 5) ^ 48 * (295 / 296) ^ 9 ∧
      (Matrix.diagonal fun _ : Fin 3 => (2 / 5 : ℝ) ^ 16 * (295 / 296) ^ 3).det =
        (2 / 5) ^ 48 * (295 / 296) ^ 9 := by
  constructor
  · ring
  · rw [colour_word]
    ring

end Comparison.GroupsContinuumLaw
