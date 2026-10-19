module

public import Comparison.Existence.Planes

/-!
# Book XII. The plane contrasts: `k·k = k` (Proposition 73)

`k(g) = (1 + sgn g + 5χ_[3,2](g))/120` (`kk g = 120 k(g)`, `Planes.lean`) is idempotent in the
algebra of the relabellings: `k_idem`: `Σ_h k(h) k(h⁻¹g) = k(g)` for every relabelling `g`.

The check runs over all `120 × 120` pairs. To keep it short, `kk_eq_kc` first reads `120 k(g)` off
the lines `g` fixes and the lines `g²` fixes (`kc`), which tell the seven types of relabelling apart
(`class_cases`); the sums are then checked type by type (`conv_*`).
-/

@[expose] public section

namespace Comparison

open Finset

/-- The lines `g` fixes, as a natural number. -/
def fixN (g : Equiv.Perm (Fin 5)) : ℕ := (univ.filter fun t => g t = t).card

/-- `120 k` by the lines fixed by `g` and by `g²`. -/
def kTab : ℕ → ℕ → ℤ
  | 5, _ => 27
  | 3, _ => 5
  | 2, _ => -3
  | 1, 5 => 7
  | 1, _ => -5
  | 0, 2 => 5
  | 0, _ => 2
  | _, _ => 0

/-- `120 k(g)` read off the lines `g` and `g²` fix. -/
def kc (g : Equiv.Perm (Fin 5)) : ℤ := kTab (fixN g) (fixN (g * g))

theorem kk_eq_kc : ∀ g : Equiv.Perm (Fin 5), kk g = kc g := by
  decide +kernel

/-- The seven types: the identity, an exchange, a 3-cycle, two exchanges, a 4-cycle, a 3-cycle
with an exchange, a 5-cycle. -/
theorem class_cases : ∀ g : Equiv.Perm (Fin 5),
    fixN g = 5 ∨ fixN g = 3 ∨ fixN g = 2 ∨ (fixN g = 1 ∧ fixN (g * g) = 5) ∨
      (fixN g = 1 ∧ fixN (g * g) = 1) ∨ (fixN g = 0 ∧ fixN (g * g) = 2) ∨
      (fixN g = 0 ∧ fixN (g * g) = 0) := by
  decide +kernel

theorem conv_e : ∀ g : Equiv.Perm (Fin 5), fixN g = 5 →
    ∑ h : Equiv.Perm (Fin 5), kc h * kc (h⁻¹ * g) = 120 * kc g := by
  decide +kernel

theorem conv_exch : ∀ g : Equiv.Perm (Fin 5), fixN g = 3 →
    ∑ h : Equiv.Perm (Fin 5), kc h * kc (h⁻¹ * g) = 120 * kc g := by
  decide +kernel

theorem conv_cyc3 : ∀ g : Equiv.Perm (Fin 5), fixN g = 2 →
    ∑ h : Equiv.Perm (Fin 5), kc h * kc (h⁻¹ * g) = 120 * kc g := by
  decide +kernel

theorem conv_exch2 : ∀ g : Equiv.Perm (Fin 5), fixN g = 1 → fixN (g * g) = 5 →
    ∑ h : Equiv.Perm (Fin 5), kc h * kc (h⁻¹ * g) = 120 * kc g := by
  decide +kernel

theorem conv_cyc4 : ∀ g : Equiv.Perm (Fin 5), fixN g = 1 → fixN (g * g) = 1 →
    ∑ h : Equiv.Perm (Fin 5), kc h * kc (h⁻¹ * g) = 120 * kc g := by
  decide +kernel

theorem conv_cyc3exch : ∀ g : Equiv.Perm (Fin 5), fixN g = 0 → fixN (g * g) = 2 →
    ∑ h : Equiv.Perm (Fin 5), kc h * kc (h⁻¹ * g) = 120 * kc g := by
  decide +kernel

theorem conv_cyc5 : ∀ g : Equiv.Perm (Fin 5), fixN g = 0 → fixN (g * g) = 0 →
    ∑ h : Equiv.Perm (Fin 5), kc h * kc (h⁻¹ * g) = 120 * kc g := by
  decide +kernel

/-- **`k·k = k`:** `Σ_h k(h) k(h⁻¹g) = k(g)` for every relabelling `g`, written times `120²`. -/
theorem k_idem (g : Equiv.Perm (Fin 5)) :
    ∑ h : Equiv.Perm (Fin 5), kk h * kk (h⁻¹ * g) = 120 * kk g := by
  simp only [kk_eq_kc]
  rcases class_cases g with h | h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact conv_e g h
  · exact conv_exch g h
  · exact conv_cyc3 g h
  · exact conv_exch2 g h1 h2
  · exact conv_cyc4 g h1 h2
  · exact conv_cyc3exch g h1 h2
  · exact conv_cyc5 g h1 h2

end Comparison

end
