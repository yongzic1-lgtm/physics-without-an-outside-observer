import Comparison.System.Postulates
import Comparison.Existence.Excursion
import Comparison.Existence.AvailableTransitions
import Comparison.Existence.Holds
import Comparison.Existence.Table
import Comparison.Law.Rule
import Comparison.Formulas.Clocks
import Comparison.Article.Pieces

/-!
# The proof system, the existence layer: Definitions 17 to 30

The objects of the Definitions 17 to 30,
named once, in the namespace `Comparison.System.Existence`; each reuses the project's definition where one
exists. The postulates of existence P4 and P5 are in `System/Postulates.lean` (`IsFact`, `Connection`,
`Connection.rename`, `hol`; `Steps`, `ChangesEachStep`, `relAt`, `stateAt`, `IsHistory`).

* Definition 17, a **step**: the line `γ_t` applied to one system, `γ_t ⊗ 1` on the two-spinor states of that system
  with another (`lineOnRel t`); on the sixteen two-spinor states it is the transition `transition t` (Prop. 14).
* Definition 18, a **world line**: `relLine w = (γ_{t_k} ⋯ γ_{t_{j+1}} ⊗ 1) Ω` for the word
  `w = [t_k, …, t_{j+1}]` of the steps between two moments, newest first; `between t j k` is that word for a
  step sequence `t` (A's `Steps`), so `relLine (between t j k)` is `r_{kj}`.
* Definition 19, a **walk**: a word, its length, its continuations (`words`, `IsHistory = Reduced`).
* Definition 20, the **last-step direction** and the **plane** of a line: its last step and the plane of its last two steps
  (`lastDirectionOf`, `planeOf`).
* Definition 21, a **vertex**: two moments are at one vertex when `(6 − L) r = 0` (`AtOnePlace`).
* Definition 22, an **excursion** (`IsExcursion`, `excursions`); Definition 23, the **coin** (`coin`).
* Definition 24, **gauge, connection, holonomy** (`CandidateSystem.Frame`, `Connection`, `hol`).
* Definition 25, the **curvature** `F_st(x) = hol(x; tsts) − 1` (`curv`, with the vertices of the square
  `squarePlaces`).
* Definition 26, the **vertical step and the parallel rotation** on the sixty-four sets: in
  `System/Existence/Ext/` (`SysExt.εv`, `SysExt.ιv`, `SysExt.Jv`, `SysExt.Tx`, `SysExt.degreeProj`, `SysExt.Nx`,
  `SysExt.extMap`).
* Definition 27, the **mass form** (`massForm`).
* Definition 28, a **clock** of a division (`IsClock`).
* Definition 29, the **divided set** and the **counterpart** of a two-spinor state (`dividedSet`, `twin`), with the plane's
  exception; `twinOther` is the other description of a plane's counterpart.
* Definition 30, the **phase** of a divided set `z_S = i^{|S|}` (`Law.zS`).
-/

namespace Comparison.System.Existence

open Matrix Complex Kronecker

/-! ## Definitions 17 to 21 -/

/-- **Definition 17, a step:** the line `γ_t` applied to one system, `γ_t ⊗ 1` on the two-spinor states. -/
noncomputable abbrev stepOn (t : Fin 5) : Matrix Two Two ℂ := lineOnRel t

theorem stepOn_eq (t : Fin 5) : stepOn t = γ t ⊗ₖ (1 : Matrix Four Four ℂ) := rfl

/-- **Definition 18:** the two-spinor state of a later moment of a line to an earlier one, for the word of the steps
between them, newest first: `r = (γ_{t_k} ⋯ γ_{t_{j+1}} ⊗ 1) Ω`; the singlet for the empty word. -/
noncomputable def relLine (w : List (Fin 5)) : Two → ℂ := ((w.map γ).prod ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω

/-- The word of the steps of a step sequence between the moments `j` and `k`, newest first:
`[t (k − 1), …, t j]` (A's `Steps`: `t i` is the step from the moment `i` to the moment `i + 1`). -/
def between (t : Steps) (j k : ℕ) : List (Fin 5) := ((List.range (k - j)).map fun i => t (j + i)).reverse

/-- The two-spinor state of the moment `k` to the moment `j` of a world line, `r_{kj}`. -/
noncomputable def rLine (t : Steps) (j k : ℕ) : Two → ℂ := relLine (between t j k)

/-- **Definition 20:** the last-step direction of a walk is its last step. -/
def lastDirectionOf (w : List (Fin 5)) : Option (Fin 5) := w.head?

/-- **Definition 20:** the plane of a walk is the plane of its last two steps. -/
def planeOf : List (Fin 5) → Option (Finset (Fin 5))
  | h :: k :: _ => some {h, k}
  | _ => none

/-- **Definition 21:** two moments are at one vertex when their two-spinor state has no disagreement. -/
def AtOnePlace (r : Two → ℂ) : Prop := disagreement *ᵥ r = 0

/-- The vector state `ℓ_t = (γ_t ⊗ 1) Ω`. -/
noncomputable def ell (t : Fin 5) : Two → ℂ := (γ t ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω

/-- The four lines other than `t`, `T_t = g_t`. -/
def T (t : Fin 5) : Finset (Fin 5) := Finset.univ.erase t

/-- The set of the steps of a word, `S(w) = T_{t_k} △ ⋯ △ T_{t_1}`. -/
def Sw (w : List (Fin 5)) : Finset (Fin 5) := w.foldr (fun t S => symmDiff S (T t)) ∅

/-! ## Definition 25: curvature -/

/-- The five vertices of the shortest closed walk `tsts` from the vertex `x`: `x`, then the steps `t`, `s`, `t`,
`s`. -/
def squarePlaces (x : Fin 16) (s t : Fin 5) : List (Fin 16) :=
  [x, transition t x, transition s (transition t x), transition t (transition s (transition t x)), transition s (transition t (transition s (transition t x)))]

/-- **Definition 25, the curvature** at the vertex `x` in the directions `s, t`:
`F_st(x) = hol(x; tsts) − 1`. -/
noncomputable def curv {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (c : Connection (Fin 16) (Matrix n n R)ˣ) (x : Fin 16) (s t : Fin 5) : Matrix n n R :=
  ((hol c (squarePlaces x s t) : (Matrix n n R)ˣ) : Matrix n n R) - 1

/-! ## Definition 28: a clock -/

/-- **Definition 28:** a clock of the division `D` of the six is a nonzero kept generator that commutes with every
kept generator. -/
def IsClock (D : Finset (Fin 6)) (X : Matrix (Fin 6) (Fin 6) ℝ) : Prop := X ≠ 0 ∧ Formulas.CentralAt D X

/-! ## Definition 29: divided set and counterpart -/

/-- The division a two-spinor state holds, named by the lines it disagrees on (the singlet undivided): `n = 0` and the line
`u` at `u + 1` (`Article/Pieces.lean`: `heldDiv`). -/
abbrev held (k : Fin 16) : Finset (Fin 6) := Article.heldDiv k

/-- **Definition 29, the divided set** of the two-spinor state `e_S`: the shorter of the two descriptions `S` and
`{n} ∪ (the lines outside S)` of its division (`Article/Pieces.lean`: `dividedSetOf`). -/
abbrev dividedSet (k : Fin 16) : Finset (Fin 6) := Article.dividedSetOf k

/-- **Definition 29, the counterpart** of a divided set: the singlet added or removed, except that the counterpart of a plane `{a, b}`
is named by the three lines outside it, `C`, rather than by `{n, a, b}`. -/
def twin (S : Finset (Fin 6)) : Finset (Fin 6) :=
  if (0 : Fin 6) ∈ S then S.erase 0 else if S.card = 2 then (insert 0 S)ᶜ else insert 0 S

/-- The other description of the counterpart, the singlet added or removed in every case (`Law/Rule.lean`: `twin`): at a plane it
is `{n, a, b}`, the other orientation `q̄` of the square root of the sign. -/
abbrev twinOther (S : Finset (Fin 6)) : Finset (Fin 6) := Law.twin S

/-- **Definition 30, the phase of a divided set**, `z_S = i^{|S|}`. -/
noncomputable abbrev zS (S : Finset (Fin 6)) : ℂ := Law.zS S

/-- A divided set is even or odd with its number of elements. -/
def IsEven (S : Finset (Fin 6)) : Prop := Even S.card

/-! ## The sign of a division on the six, read on P1's real six -/

/-- The sign `θ_D` of a division of the six at the direction `c`: `−1` on the divided part. -/
def thetaAt (D : Finset (Fin 6)) (c : Fin 6) : ℂ := if c ∈ D then -1 else 1

end Comparison.System.Existence
