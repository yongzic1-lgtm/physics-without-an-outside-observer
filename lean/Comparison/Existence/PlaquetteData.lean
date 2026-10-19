module

public import Comparison.Existence.Gauge

/-!
# Book XI. The law in small phases: the finite data (Proposition 62)

Everything here is a finite check
(`decide`) on the sixteen two-spinor states, their forty links and their forty squares; the real and complex
statements are in `Plaquette.lean`.

* `sadjZ`: the signed step `A = Σ_t B[ν]_t` in the two-spinor state basis (`sadjZ_eq`); `sadjZ_symm`,
  `sadjZ_diag`, `sadjZ_sq` (**`A² = 5`**), `sadjZ_tri` (no triangles).
* `linkU`, `linkV`: the forty links, `links_complete`, `links_distinct`; `linkZ ℓ = E_uv − E_vu`.
* `sqX`, `sqS`, `sqT`, `sqVert`: the forty squares `tsts`, `squares_complete`, `squares_distinct`.
* `cZ q ℓ`: the circulation matrix `C`; `GZ = CᵀC`; `B4Z ℓ m = tr(A H_ℓ A H_m)` in closed form.
* `B4Z_eq`: **`B₄ = 10·1 − 2CᵀC`**; `NZ_eq`; `cZ_div`: `C · grad = 0` on the integers.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J

/-! ## The signed adjacency, the forty links and the forty squares -/

/-- The signed step `A = Σ_t B[ν]_t` on the sixteen two-spinor states. -/
def sadjZ : Matrix (Fin 16) (Fin 16) ℤ :=
  !![0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, -1, -1, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -1, -1, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, -1;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1;
    0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1;
    0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1;
    0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, -1, 0;
    0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0;
    0, 0, -1, 1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, -1;
    0, 0, -1, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 0;
    0, 0, -1, 0, 0, 1, 0, -1, 1, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, -1, 1, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0;
    0, 0, 0, -1, 0, 1, 1, 0, -1, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, -1, 1, -1, 1, 0, 0, -1, 0, 0, 0, 0, 0]

/-- The entries of `A` as a function (for the finite checks). -/
def sadjF (x y : Fin 16) : ℤ := sadjZ x y

/-- The table is the signed step: `A_{k'k} = Σ_t [k' = transition t k] ν(k, t)`. -/
theorem sadjZ_eq :
    sadjZ = Matrix.of fun x y => ∑ t : Fin 5, if x = transition t y then transitionSign t y else 0 := by
  decide

theorem sadjZ_transpose : sadjZᵀ = sadjZ := by decide

theorem sadjZ_symm (x y : Fin 16) : sadjZ x y = sadjZ y x := by
  have h := congrFun (congrFun sadjZ_transpose y) x
  rwa [Matrix.transpose_apply] at h

theorem sadjZ_diag : ∀ x : Fin 16, sadjZ x x = 0 := by decide

/-- **`A² = 5`.** -/
theorem sadjZ_sq : sadjZ * sadjZ = (5 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by decide

/-- **No triangles.** -/
theorem sadjZ_tri : ∀ x y z : Fin 16, sadjZ x y * sadjZ y z * sadjZ z x = 0 := by decide

/-- The forty links `(u, v)`, `u < v`. -/
def linkU : Fin 40 → Fin 16 :=
  ![0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 7, 7, 7, 8,
    8, 8, 9, 9, 9, 10, 11, 12]

def linkV : Fin 40 → Fin 16 :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 6, 10, 11, 12, 7, 10, 13, 14, 8, 11, 13, 15, 9, 12, 14, 15, 13, 14,
    15, 11, 12, 15, 10, 12, 14, 10, 11, 13, 15, 14, 13]

theorem links_ok : ∀ l : Fin 40,
    linkU l < linkV l ∧ sadjZ (linkU l) (linkV l) * sadjZ (linkU l) (linkV l) = 1 := by decide

/-- **The table lists exactly the forty links.** -/
theorem links_complete : ∀ x y : Fin 16, x < y → sadjF x y ≠ 0 →
    ∃ l : Fin 40, linkU l = x ∧ linkV l = y := by decide

theorem links_distinct : ∀ l m : Fin 40, linkU l = linkU m → linkV l = linkV m → l = m := by
  decide

/-- The link `ℓ` as an antisymmetric integer matrix: `E_uv − E_vu`. -/
def linkZ (l : Fin 40) : Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.of fun x y => if x = linkU l ∧ y = linkV l then 1 else if x = linkV l ∧ y = linkU l then -1
    else 0

/-- The forty squares, each from a vertex and two steps `s ≠ t`. -/
def sqX : Fin 40 → Fin 16 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4,
    4, 4, 5, 5, 5, 5, 5, 5]

def sqS : Fin 40 → Fin 5 :=
  ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 0, 0, 0, 2, 2, 3, 0, 0, 0, 1, 1, 3, 0, 0, 0, 1,
    1, 2, 0, 0, 0, 1, 1, 2]

def sqT : Fin 40 → Fin 5 :=
  ![1, 2, 3, 4, 2, 3, 4, 3, 4, 4, 2, 3, 4, 3, 4, 4, 2, 3, 4, 3, 4, 4, 1, 3, 4, 3, 4, 4, 1, 2, 4, 2,
    4, 4, 1, 2, 3, 2, 3, 3]

/-- The four vertices of the square `q`, in order around it. -/
def sqVert (q : Fin 40) : Fin 4 → Fin 16 :=
  ![sqX q, transition (sqS q) (sqX q), transition (sqT q) (transition (sqS q) (sqX q)),
    transition (sqS q) (transition (sqT q) (transition (sqS q) (sqX q)))]

theorem squares_closed : ∀ q : Fin 40,
    sqS q ≠ sqT q ∧ transition (sqT q) (sqVert q 3) = sqX q := by decide

/-- **The table lists exactly the forty squares** of Proposition 38. -/
theorem squares_complete : ∀ (x : Fin 16) (s t : Fin 5), s ≠ t →
    ∃ q : Fin 40, square x s t = square (sqX q) (sqS q) (sqT q) := by
  decide +kernel

theorem squares_distinct : ∀ q q' : Fin 40,
    square (sqX q) (sqS q) (sqT q) = square (sqX q') (sqS q') (sqT q') → q = q' := by
  decide +kernel

/-- The coefficient of the link `ℓ` in the sum of phases around the square `q`. -/
def cZ (q l : Fin 40) : ℤ :=
  linkZ l (sqVert q 1) (sqVert q 0) + linkZ l (sqVert q 2) (sqVert q 1) +
    linkZ l (sqVert q 3) (sqVert q 2) + linkZ l (sqVert q 0) (sqVert q 3)

/-- `CᵀC`. -/
def GZ (l m : Fin 40) : ℤ := ∑ q : Fin 40, cZ q l * cZ q m

/-- The four-step closed walks through the links `ℓ` and `m`, `tr(A H_ℓ A H_m)`. -/
def B4Z (l m : Fin 40) : ℤ :=
  sadjZ (linkU l) (linkV l) * sadjZ (linkU m) (linkV m) *
    (sadjZ (linkV m) (linkU l) * sadjZ (linkV l) (linkU m) -
      sadjZ (linkU m) (linkU l) * sadjZ (linkV l) (linkV m) -
      sadjZ (linkV m) (linkV l) * sadjZ (linkU l) (linkU m) +
      sadjZ (linkU m) (linkV l) * sadjZ (linkU l) (linkV m))

/-- **The four-step walks against the squares:** `B₄ = 10·1 − 2CᵀC`. -/
theorem B4Z_eq : ∀ l m : Fin 40, B4Z l m = 10 * (if l = m then 1 else 0) - 2 * GZ l m := by
  decide +kernel

/-- `Σ_{x,y} A_xy² (E_ℓ)_xy (E_m)_xy = 2δ_ℓm`. -/
theorem NZ_eq : ∀ l m : Fin 40,
    ∑ x : Fin 16, ∑ y : Fin 16, sadjZ x y * sadjZ x y * linkZ l x y * linkZ m x y =
      2 * (if l = m then 1 else 0) := by
  decide +kernel

/-- A gradient sums to zero around every square. -/
theorem cZ_div : ∀ (q : Fin 40) (x : Fin 16),
    ∑ l : Fin 40, cZ q l * ((if linkV l = x then 1 else 0) - (if linkU l = x then 1 else 0)) = 0 := by
  decide +kernel

end Comparison

end
