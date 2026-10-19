import Comparison.System.Existence.Six
import Comparison.System.Geometry.RealForm

/-!
# The proof system, the existence layer: Proposition 40 whole

The ten rotations that keep the singlet have their planes among the
five directions, so counterparts (a division and its toggle of the singlet) keep the same ten (`twins_kept_ten`). The real forms of the
six rows: the division `S` and the division of the lines it divides, `D = divLines S`, have the same real form
(`realFormAlg_divLines`: the same division, or complements, which have one real form, `realFormAlg_compl`), so
Definition 15's real form of the row is `{X : tr X = 0, X†h_D + h_DX = 0}` for `|D|` even and
`{X : tr X = 0, XC_D = C_DX}` for `|D|` odd (`realFormAlg_lines_even`, `realFormAlg_lines_odd`), the real span
of fifteen generators; the balanced directions of `S` are the `v` with `|v off S| = |v on S|`, whose lines are
`(S^{5−k} × S^{k−1})/ℤ₂`, `k = |S|`.
-/

namespace Comparison.System.Existence

open Matrix Complex

/-! ## The counterparts keep the same ten -/

theorem plane_ten_ne_singlet : ∀ f : Fin 10, (plane (Sum.inr f)).1 ≠ 0 ∧ (plane (Sum.inr f)).2 ≠ 0 := by
  decide

/-- **Counterparts keep the same ten:** toggling the singlet changes no rotation among the ten that keep it. -/
theorem twins_kept_ten (S : Finset (Fin 6)) (f : Fin 10) :
    Kept S (Sum.inr f) ↔ Kept (symmDiff S {0}) (Sum.inr f) := by
  obtain ⟨h1, h2⟩ := plane_ten_ne_singlet f
  rw [kept_iff, kept_iff]
  simp [Finset.mem_symmDiff, h1, h2]

/-! ## The real forms of the six -/

theorem linesDiv_eq_divOf : ∀ D : Finset (Fin 5), Geometry.linesDiv D = JointCells.Patterns.divOf D := by
  decide +kernel

/-- **A row and the division of its lines have one real form.** -/
theorem realFormAlg_divLines (S : Finset (Fin 6)) :
    Geometry.realFormAlg (Geometry.projOf (Geometry.linesDiv (divLines S))) =
      Geometry.realFormAlg (Geometry.projOf S) := by
  rw [linesDiv_eq_divOf, divOf_divLines]
  split_ifs
  · exact Geometry.realFormAlg_compl S
  · rfl

theorem realForm_row_even (S : Finset (Fin 6)) (hS : (divLines S).card % 2 = 0) (X : Matrix Four Four ℂ) :
    X ∈ Geometry.realFormAlg (Geometry.projOf S) ↔
      X.trace = 0 ∧ Xᴴ * hermForm (divLines S) + hermForm (divLines S) * X = 0 := by
  rw [← realFormAlg_divLines]
  exact Geometry.realFormAlg_lines_even _ hS X

theorem realForm_row_odd (S : Finset (Fin 6)) (hS : (divLines S).card % 2 = 1) (X : Matrix Four Four ℂ) :
    X ∈ Geometry.realFormAlg (Geometry.projOf S) ↔
      X.trace = 0 ∧ X * (gammaD (divLines S) * Comparison.J) = (gammaD (divLines S) * Comparison.J) * X.map star := by
  rw [← realFormAlg_divLines]
  exact Geometry.realFormAlg_lines_odd _ hS X

theorem six_divLines (h k : Fin 5) (hhk : h ≠ k) :
    (sixOf h k).map divLines = [∅, Finset.univ, Finset.univ.erase h, {h}, {h, k}, Finset.univ \ {h, k}] := by
  revert h k
  decide +kernel

/-! ## The balanced directions -/

theorem balanced_iff (S : Finset (Fin 6)) (v : Fin 6 → ℝ) :
    Geometry.Balanced (Geometry.projOf S) v ↔
      v ≠ 0 ∧ ∑ a, (if a ∈ S then 0 else v a ^ 2) = ∑ a, (if a ∈ S then v a ^ 2 else 0) := by
  rw [Geometry.Balanced, Geometry.projOf, Geometry.metric_ofSet, Complex.ofReal_eq_zero, sub_eq_zero]

/-! ## Proposition 40 -/

/-- **Proposition 40 (the table of the six).** For every last-step direction `h` and plane `{h, k}`, the six divisions a line holds,
`{}`, `{n}`, `{h, n}`, `{h}`, `F = {h, k}`, `C`, have: the types `0¦6, 1¦5, 2¦4, 1¦5, 2¦4, 3¦3`; the time-like
part (the smaller part, where `θ_S = −1`): none, the singlet, the singlet and `h`, the last-step direction, the plane, none; the loops
`−1/+1`: `15/0, 10/5, 7/8, 10/5, 7/8, 6/9` (a loop `(f_xf_y)²` is `−1` within a side, `+1` across); the phases
`z_S = 1, i, −1, i, −1, −i`; kept/moved of the fifteen `15/0, 10/5, 7/8, 10/5, 7/8, 6/9` and of the ten
`10/0, 10/0, 6/4, 6/4, 4/6, 4/6`, counterparts keeping the same ten; a centre of the kept rotations of dimension
`0, 0, 1, 0, 1, 0`, the clocks `E_{n h} − E_{h n}` at `{h, n}` and `E_{h k} − E_{k h}` at `F` (the rotations of `iγ_h`
and `γ_hγ_k`, Prop. 41); every moved unit rotation has `M_S = 2`; for every connection the curvature splits as
`A = A_k + A_m`, `F_k = F(A_k) + (A_m ∧ A_m)_k`, `F_m = D_{A_k}A_m` (the derivatives of the parts are the parts of
the derivative, `keptPart_hasFDerivAt`, `movedPart_hasFDerivAt`); the rows divide the lines `∅`, all five, all but
`h`, `{h}`, `{h, k}`, `C`, and the real form of each row (Definition 15) is the real span of fifteen generators,
`{X : tr X = 0, X†h_D + h_DX = 0}` for the even line sets `D` (`h_D` Hermitian, `h_D² = 1`, trace zero for
`|D| = 2, 4`) and `{X : tr X = 0, XC_D = C_DX}` for the odd ones (`C_D² = −1, −1, +1` at `|D| = 1, 5, 3`); the
balanced directions of each row are the `v ≠ 0` with `|v off S| = |v on S|`, and two of them span one line exactly
when their normalized representatives agree up to sign: the balanced lines are `(S^{5−k} × S^{k−1})/ℤ₂`, `k = |S|`.
The real forms as groups (`SU(4)`, `SU*(4)`, `SU(2,2)`, `SL(4, ℝ)`) are in the geometry layer.

Recognition: `{}` the universality of gravity; `{n}` the sign of time of every pair and the sphere of lines; `{h}`
the ten rotations split at the last-step direction, `6 + 4`, spin connection and co-frame; `{h, n}` the line's own clock; `F` the common
time and light; `C` two times and no clock, colour; the real forms `su(4)`, `sl(2, ℍ)`, `su(2,2)`, `sl(4, ℝ)` and the
balanced directions `S⁴`, `(S¹ × S³)/ℤ₂`, `(S² × S²)/ℤ₂`. Uses Props. 21, 22, 27, 34, 35, 39, Definitions 15, 28. -/
theorem prop_40_full (h k : Fin 5) (hhk : h ≠ k) :
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
    (∀ S : Finset (Fin 6), ∀ f : Fin 10, Kept S (Sum.inr f) ↔ Kept (symmDiff S {0}) (Sum.inr f)) ∧
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
          (fun μ ν => movedPart (theta ℂ S) (dA μ ν)) μ ν) ∧
    (sixOf h k).map divLines = [∅, Finset.univ, Finset.univ.erase h, {h}, {h, k}, Finset.univ \ {h, k}] ∧
    (∀ S ∈ sixOf h k, Geometry.realFormAlg (Geometry.projOf S) =
        (Submodule.span ℝ (Set.range (Geometry.realGen6 S)) : Set (Matrix Four Four ℂ)) ∧
      Module.finrank ℝ (Submodule.span ℝ (Set.range (Geometry.realGen6 S))) = 15) ∧
    (∀ S ∈ sixOf h k, (divLines S).card % 2 = 0 →
      (∀ X : Matrix Four Four ℂ, X ∈ Geometry.realFormAlg (Geometry.projOf S) ↔
        X.trace = 0 ∧ Xᴴ * hermForm (divLines S) + hermForm (divLines S) * X = 0) ∧
      (hermForm (divLines S))ᴴ = hermForm (divLines S) ∧ hermForm (divLines S) * hermForm (divLines S) = 1 ∧
      ((divLines S).card ≠ 0 → (hermForm (divLines S)).trace = 0)) ∧
    (∀ S ∈ sixOf h k, (divLines S).card % 2 = 1 →
      (∀ X : Matrix Four Four ℂ, X ∈ Geometry.realFormAlg (Geometry.projOf S) ↔
        X.trace = 0 ∧ X * (gammaD (divLines S) * Comparison.J) = (gammaD (divLines S) * Comparison.J) * X.map star) ∧
      ∀ v : Four → ℂ, Cop (divLines S) (Cop (divLines S) v) = (countSign (divLines S).card : ℂ) • v) ∧
    countSign 1 = -1 ∧ countSign 3 = 1 ∧ countSign 5 = -1 ∧
    (∀ S ∈ sixOf h k, ∀ v : Fin 6 → ℝ, Geometry.Balanced (Geometry.projOf S) v ↔
      v ≠ 0 ∧ ∑ a, (if a ∈ S then 0 else v a ^ 2) = ∑ a, (if a ∈ S then v a ^ 2 else 0)) ∧
    (∀ S ∈ sixOf h k, ∀ v w : EuclideanSpace ℝ (Fin (6 - S.card)) × EuclideanSpace ℝ (Fin S.card),
      v ≠ 0 → ‖v.1‖ = ‖v.2‖ → w ≠ 0 → ‖w.1‖ = ‖w.2‖ →
        ((∃ c : ℝ, c ≠ 0 ∧ w = c • v) ↔ (GroupsContinuumLaw.nrmPQ w = GroupsContinuumLaw.nrmPQ v ∨ GroupsContinuumLaw.nrmPQ w = -GroupsContinuumLaw.nrmPQ v))) ∧
    (∀ S ∈ sixOf h k, ∀ v : EuclideanSpace ℝ (Fin (6 - S.card)) × EuclideanSpace ℝ (Fin S.card),
      v ≠ 0 → ‖v.1‖ = ‖v.2‖ → 0 < ‖v.1‖ ∧ ‖(GroupsContinuumLaw.nrmPQ v).1‖ = 1 ∧ ‖(GroupsContinuumLaw.nrmPQ v).2‖ = 1) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13⟩ := prop_40 h k hhk
  refine ⟨t1, t2, t3, t4, t5, t6, t7, t8, twins_kept_ten, t9, t10, t11, t12, t13, six_divLines h k hhk,
    fun S _ => ⟨Geometry.realFormAlg_ofSet S, Geometry.finrank_realFormSpan S⟩,
    fun S _ hS => ⟨realForm_row_even S hS, Geometry.hermForm_props _ hS⟩,
    fun S _ hS => ⟨realForm_row_odd S hS, C_sq _⟩, by decide, by decide, by decide,
    fun S _ v => balanced_iff S v,
    fun S _ v w hv hvn hw hwn => GroupsContinuumLaw.null_line_iff v w hv hvn hw hwn,
    fun S _ v hv hn => GroupsContinuumLaw.null_normalize v hv hn⟩

end Comparison.System.Existence
