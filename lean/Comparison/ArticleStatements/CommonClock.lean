import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The common clock (statement 12, Proposition 91)

After statement 12 of the article: the common clock on a plane is a transported rotation; its phases agree
globally exactly when their product around every loop is one. On a graph of vertices with a phase `g(x, y)`
carried along each link (in a commutative group, the clock's phases), reversible, `g(y, x) = g(x, y)⁻¹`:

* `walkProd`: the phase carried along a walk, the product of its link phases; `walkProd_cons`,
  `walkProd_append`, `walkProd_concat`, `walkProd_reverse`.
* `walkProd_of_clock`: with a common clock `φ`, `g(x, y) = φ(y)/φ(x)` on every link, the phase along a walk
  is `φ(end)/φ(start)`; `loops_close_of_clock`: **around every closed walk it is one**.
* `clock_of_loops_close`: **conversely, on a connected graph where every closed walk carries phase one,
  a common clock exists** (choose a walk from one vertex to each other vertex; a loop through any link fixes
  the link's phase).
* `clock_iff_loops`: **a common clock exists exactly when every loop closes**; `clock_unique`: on a
  connected graph it is unique up to one overall phase.
-/

namespace Comparison.ArticleStatements.Clock

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {K : Type*} [CommGroup K]

/-- **The phase carried along a walk**: the product of its link phases `g(x, y)`. -/
def walkProd (g : V → V → K) {u v : V} (p : G.Walk u v) : K :=
  (p.darts.map fun d => g d.fst d.snd).prod

theorem walkProd_nil (g : V → V → K) (u : V) : walkProd g (Walk.nil : G.Walk u u) = 1 := rfl

theorem walkProd_cons (g : V → V → K) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkProd g (Walk.cons h p) = g u v * walkProd g p := by
  simp [walkProd]

theorem walkProd_append (g : V → V → K) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkProd g (p.append q) = walkProd g p * walkProd g q := by
  simp [walkProd, List.prod_append]

theorem walkProd_concat (g : V → V → K) {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    walkProd g (p.concat h) = walkProd g p * g v w := by
  rw [Walk.concat_eq_append, walkProd_append, walkProd_cons, walkProd_nil, mul_one]

/-- **Reversing a walk inverts its phase**, for reversible link phases. -/
theorem walkProd_reverse (g : V → V → K) (hg : ∀ x y, g y x = (g x y)⁻¹) {u v : V}
    (p : G.Walk u v) : walkProd g p.reverse = (walkProd g p)⁻¹ := by
  induction p with
  | nil => simp [walkProd]
  | @cons a b c h p ih =>
    rw [Walk.reverse_cons, walkProd_append, ih, walkProd_cons, walkProd_cons, walkProd_nil, mul_one,
      hg a b, mul_inv_rev]

/-- **With a common clock the phase along a walk is `φ(end)/φ(start)`.** -/
theorem walkProd_of_clock (g : V → V → K) (φ : V → K) (hφ : ∀ x y, G.Adj x y → g x y = φ y / φ x)
    {u v : V} (p : G.Walk u v) : walkProd g p = φ v / φ u := by
  induction p with
  | nil => rw [walkProd_nil, div_self']
  | @cons a b c h p ih =>
    rw [walkProd_cons, ih, hφ a b h, div_mul_div_comm, mul_comm (φ b) (φ c), mul_div_mul_right_eq_div]

/-- **With a common clock every loop closes:** the phase around every closed walk is one. -/
theorem loops_close_of_clock (g : V → V → K) (φ : V → K) (hφ : ∀ x y, G.Adj x y → g x y = φ y / φ x)
    {u : V} (p : G.Walk u u) : walkProd g p = 1 := by
  rw [walkProd_of_clock g φ hφ p, div_self']

/-- **If every loop closes, a common clock exists** (on a connected graph, for reversible phases). -/
theorem clock_of_loops_close (g : V → V → K) (hg : ∀ x y, g y x = (g x y)⁻¹)
    (hconn : G.Preconnected) (x₀ : V) (hloop : ∀ (u : V) (p : G.Walk u u), walkProd g p = 1) :
    ∃ φ : V → K, ∀ x y, G.Adj x y → g x y = φ y / φ x := by
  refine ⟨fun v => walkProd g (hconn x₀ v).some, fun x y h => ?_⟩
  have hc := hloop x₀ (((hconn x₀ x).some.concat h).append (hconn x₀ y).some.reverse)
  rw [walkProd_append, walkProd_concat, walkProd_reverse g hg] at hc
  rw [eq_div_iff_mul_eq', mul_comm]
  exact mul_inv_eq_one.mp hc

/-- **A common clock exists exactly when every loop closes** (Proposition 91). -/
theorem clock_iff_loops (g : V → V → K) (hg : ∀ x y, g y x = (g x y)⁻¹) (hconn : G.Preconnected)
    (x₀ : V) :
    (∃ φ : V → K, ∀ x y, G.Adj x y → g x y = φ y / φ x) ↔
      ∀ (u : V) (p : G.Walk u u), walkProd g p = 1 := by
  constructor
  · rintro ⟨φ, hφ⟩ u p
    exact loops_close_of_clock g φ hφ p
  · exact clock_of_loops_close g hg hconn x₀

/-- **The common clock is unique up to one overall phase** on a connected graph. -/
theorem clock_unique (g : V → V → K) (hconn : G.Preconnected) (φ ψ : V → K)
    (hφ : ∀ x y, G.Adj x y → g x y = φ y / φ x) (hψ : ∀ x y, G.Adj x y → g x y = ψ y / ψ x)
    (u v : V) : ψ v / φ v = ψ u / φ u := by
  have h1 := walkProd_of_clock g φ hφ (hconn u v).some
  have h2 := walkProd_of_clock g ψ hψ (hconn u v).some
  rw [h1] at h2
  rw [div_eq_div_iff_mul_eq_mul] at h2 ⊢
  rw [← h2, mul_comm]

end Comparison.ArticleStatements.Clock

#print axioms Comparison.ArticleStatements.Clock.walkProd_nil
#print axioms Comparison.ArticleStatements.Clock.walkProd_cons
#print axioms Comparison.ArticleStatements.Clock.walkProd_append
#print axioms Comparison.ArticleStatements.Clock.walkProd_concat
#print axioms Comparison.ArticleStatements.Clock.walkProd_reverse
#print axioms Comparison.ArticleStatements.Clock.walkProd_of_clock
#print axioms Comparison.ArticleStatements.Clock.loops_close_of_clock
#print axioms Comparison.ArticleStatements.Clock.clock_of_loops_close
#print axioms Comparison.ArticleStatements.Clock.clock_iff_loops
#print axioms Comparison.ArticleStatements.Clock.clock_unique
