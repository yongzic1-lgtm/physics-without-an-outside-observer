import Mathlib

/-!
# Every closed walk counted once — the Euler product (Eq. 12, Prop. 52)

A closed walk of length `r` is a word `c : Fin r → α` read cyclically; `ext c n = c (n mod r)`.
Its least period `d = minPer c` divides `r`, its root `root c : Fin d → α` is primitive (no shorter
period), and `c` is the `(r/d)`-th power of its root. Proved here:

* `HasPer.gcd`, `minPer_dvd`: periods are closed under `gcd`, so **the least period divides `r`**;
* `ext_root`, `minPer_root`, `rep_root`, `root_rep`, `minPer_rep`: **each word is the power of one
  primitive word, and each primitive word of length `d ∣ r` has exactly one power of length `r`**;
* `sum_words`: **`Σ_{c} F(c) = Σ_{d ∣ r} Σ_{p primitive of length d} F(p^{r/d})`** for every `F`;
* `cycWeight_rep`: the weight of a power is the power of the weight;
* `trace_pow_eq_sum`: **`Tr M^r = Σ_{closed words c} Π_j M(c_{j+1}, c_j)`**;
* `euler_coefficient`: **`Tr M^r = Σ_{d ∣ r} Σ_{p primitive, |p| = d} w(p)^{r/d}`**, i.e. the
  coefficient of `u^r` in `log det(I − uM)⁻¹ = Σ_r u^r Tr M^r / r` equals that of
  `Σ_{p primitive} (1/|p|) Σ_k (u^{|p|} w(p))^k / k = −Σ_{[p]} log(1 − u^{|p|} w(p))`:
  **the Euler product over the primitive closed walks**, each counted with its `|p|` rotations
  (`rotate_injective_prim`).
-/

namespace Comparison.GroupsContinuumLaw.Euler

open Finset

/-! ## Periods of functions on `ℕ` -/

section Periods

variable {α : Type*}

/-- `f` repeats after `k` steps. -/
def HasPer (f : ℕ → α) (k : ℕ) : Prop := ∀ n, f (n + k) = f n

theorem HasPer.mul {f : ℕ → α} {k : ℕ} (h : HasPer f k) (m : ℕ) : HasPer f (m * k) := by
  intro n
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, ← add_assoc, h, ih]

theorem HasPer.sub {f : ℕ → α} {k l : ℕ} (hk : HasPer f k) (hl : HasPer f l) (hkl : k ≤ l) :
    HasPer f (l - k) := by
  intro n
  rw [← hk (n + (l - k)), show n + (l - k) + k = n + l by omega, hl]

theorem HasPer.mod {f : ℕ → α} {k l : ℕ} (hk : HasPer f k) (hl : HasPer f l) :
    HasPer f (l % k) := by
  have h := (hk.mul (l / k)).sub hl (Nat.div_mul_le_self l k)
  have e : l - l / k * k = l % k := Nat.sub_eq_of_eq_add (by rw [add_comm]; exact (Nat.div_add_mod' l k).symm)
  rwa [e] at h

theorem HasPer.gcd {f : ℕ → α} {k l : ℕ} (hk : HasPer f k) (hl : HasPer f l) :
    HasPer f (Nat.gcd k l) := by
  induction k, l using Nat.gcd.induction with
  | H0 n => simpa using hl
  | H1 m n _ ih =>
    rw [Nat.gcd_rec]
    exact ih (hk.mod hl) hk

theorem HasPer.mod_eq {f : ℕ → α} {d : ℕ} (h : HasPer f d) (n : ℕ) : f n = f (n % d) := by
  conv_lhs => rw [← Nat.mod_add_div n d, mul_comm]
  exact h.mul (n / d) (n % d)

end Periods

/-! ## Words, their least period and their root -/

section Words

variable {α : Type*}

/-- The periodic extension of a word. -/
def ext {r : ℕ} (hr : 0 < r) (c : Fin r → α) : ℕ → α := fun n => c ⟨n % r, Nat.mod_lt _ hr⟩

theorem ext_per {r : ℕ} (hr : 0 < r) (c : Fin r → α) : HasPer (ext hr c) r := by
  intro n
  simp [ext]

theorem ext_lt {r : ℕ} (hr : 0 < r) (c : Fin r → α) (j : Fin r) : ext hr c j = c j := by
  simp [ext, Nat.mod_eq_of_lt j.2]

open Classical in
/-- **The least period** of a word. -/
noncomputable def minPer {r : ℕ} (hr : 0 < r) (c : Fin r → α) : ℕ :=
  Nat.find (⟨r, hr, ext_per hr c⟩ : ∃ k, 0 < k ∧ HasPer (ext hr c) k)

theorem minPer_spec {r : ℕ} (hr : 0 < r) (c : Fin r → α) :
    0 < minPer hr c ∧ HasPer (ext hr c) (minPer hr c) := by
  classical
  exact Nat.find_spec (⟨r, hr, ext_per hr c⟩ : ∃ k, 0 < k ∧ HasPer (ext hr c) k)

theorem minPer_le {r : ℕ} (hr : 0 < r) (c : Fin r → α) {k : ℕ} (hk : 0 < k)
    (h : HasPer (ext hr c) k) : minPer hr c ≤ k := by
  classical
  exact Nat.find_min' _ ⟨hk, h⟩

/-- **The least period divides every period**, in particular `r`. -/
theorem minPer_dvd_of {r : ℕ} (hr : 0 < r) (c : Fin r → α) {k : ℕ} (hk : 0 < k)
    (h : HasPer (ext hr c) k) : minPer hr c ∣ k := by
  obtain ⟨hpos, hper⟩ := minPer_spec hr c
  have hg := hper.gcd h
  have hgpos : 0 < Nat.gcd (minPer hr c) k := Nat.gcd_pos_of_pos_left _ hpos
  have hle := minPer_le hr c hgpos hg
  have hge : Nat.gcd (minPer hr c) k ≤ minPer hr c := Nat.gcd_le_left _ hpos
  have heq : Nat.gcd (minPer hr c) k = minPer hr c := le_antisymm hge hle
  rw [← heq]
  exact Nat.gcd_dvd_right _ _

theorem minPer_dvd {r : ℕ} (hr : 0 < r) (c : Fin r → α) : minPer hr c ∣ r :=
  minPer_dvd_of hr c hr (ext_per hr c)

/-- The least period depends only on the periodic extension. -/
theorem minPer_congr {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (c : Fin r → α) (e : Fin s → α)
    (h : ext hr c = ext hs e) : minPer hr c = minPer hs e := by
  apply le_antisymm
  · obtain ⟨hpos, hper⟩ := minPer_spec hs e
    exact minPer_le hr c hpos (by rw [h]; exact hper)
  · obtain ⟨hpos, hper⟩ := minPer_spec hr c
    exact minPer_le hs e hpos (by rw [← h]; exact hper)

/-- The `r`-letter power of a word of length `d`. -/
def rep {d : ℕ} (hd : 0 < d) (p : Fin d → α) (r : ℕ) : Fin r → α :=
  fun j => p ⟨j % d, Nat.mod_lt _ hd⟩

/-- The first `d` letters of a word of length `r ≥ d`. -/
def root {r d : ℕ} (hdr : d ≤ r) (c : Fin r → α) : Fin d → α := fun i => c ⟨i, by omega⟩

theorem ext_rep {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (hdr : d ∣ r) (p : Fin d → α) :
    ext hr (rep hd p r) = ext hd p := by
  funext n
  simp only [ext, rep]
  congr 2
  exact Nat.mod_mod_of_dvd n hdr

/-- **A word is the power of its root at its least period.** -/
theorem ext_root {r : ℕ} (hr : 0 < r) (c : Fin r → α) {d : ℕ} (hd : 0 < d)
    (hdr : d ∣ r) (hper : HasPer (ext hr c) d) :
    ext hd (root (Nat.le_of_dvd hr hdr) c) = ext hr c := by
  funext n
  rw [hper.mod_eq n]
  simp only [ext, root]
  congr 2
  exact (Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt n hd) (Nat.le_of_dvd hr hdr))).symm

theorem rep_root {r : ℕ} (hr : 0 < r) (c : Fin r → α) {d : ℕ} (hd : 0 < d) (hdr : d ∣ r)
    (hper : HasPer (ext hr c) d) : rep hd (root (Nat.le_of_dvd hr hdr) c) r = c := by
  funext j
  have h1 := congrFun (ext_rep hd hr hdr (root (Nat.le_of_dvd hr hdr) c)) j
  rw [ext_root hr c hd hdr hper, ext_lt, ext_lt] at h1
  exact h1

theorem root_rep {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (hdr : d ∣ r) (p : Fin d → α) :
    root (Nat.le_of_dvd hr hdr) (rep hd p r) = p := by
  funext i
  simp only [root, rep]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.2)

/-- **The root of a word at its least period is primitive.** -/
theorem minPer_root {r : ℕ} (hr : 0 < r) (c : Fin r → α) :
    minPer (minPer_spec hr c).1 (root (Nat.le_of_dvd hr (minPer_dvd hr c)) c) = minPer hr c := by
  have h := ext_root hr c (minPer_spec hr c).1 (minPer_dvd hr c) (minPer_spec hr c).2
  exact minPer_congr _ _ _ _ h

/-- **The power of a primitive word has the same least period.** -/
theorem minPer_rep {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (hdr : d ∣ r) (p : Fin d → α) :
    minPer hr (rep hd p r) = minPer hd p :=
  minPer_congr hr hd _ _ (ext_rep hd hr hdr p)

end Words

/-! ## Every word is counted once, through its primitive root -/

section Sum

variable {α : Type*} [Fintype α] [DecidableEq α] {R : Type*} [AddCommMonoid R]

open Classical in
/-- **`Σ_c F(c) = Σ_{d ∣ r} Σ_{p primitive of length d} F(p^{r/d})`.** -/
theorem sum_words {r : ℕ} (hr : 0 < r) (F : (Fin r → α) → R) :
    ∑ c : Fin r → α, F c =
      ∑ d ∈ r.divisors.attach, ∑ p ∈ (Finset.univ.filter fun p : Fin d.1 → α =>
          minPer (Nat.pos_of_mem_divisors d.2) p = d.1),
        F (rep (Nat.pos_of_mem_divisors d.2) p r) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := r.divisors.attach)
    (g := fun c => (⟨minPer hr c, Nat.mem_divisors.2 ⟨minPer_dvd hr c, hr.ne'⟩⟩ :
      {x // x ∈ r.divisors}))
    (fun c _ => Finset.mem_attach _ _)]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hd : 0 < d.1 := Nat.pos_of_mem_divisors d.2
  have hdr : d.1 ∣ r := Nat.dvd_of_mem_divisors d.2
  symm
  apply Finset.sum_nbij' (fun p => rep hd p r) (fun c => root (Nat.le_of_dvd hr hdr) c)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    apply Subtype.ext
    simp only
    rw [minPer_rep hd hr hdr, hp]
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    have hc' : minPer hr c = d.1 := congrArg Subtype.val hc
    have hper : HasPer (ext hr c) d.1 := hc' ▸ (minPer_spec hr c).2
    have h := ext_root hr c hd hdr hper
    rw [minPer_congr _ _ _ _ h, hc']
  · intro p hp
    exact root_rep hd hr hdr p
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have hc' : minPer hr c = d.1 := congrArg Subtype.val hc
    exact rep_root hr c hd hdr (hc' ▸ (minPer_spec hr c).2)
  · intro p _
    rfl

end Sum

/-! ## The trace of a power as a sum over closed words -/

section Trace

variable {α : Type*} [Fintype α] [DecidableEq α] {R : Type*} [CommRing R]

theorem prod_cons_walk (M : Matrix α α R) (n : ℕ) (y : α) (v : Fin (n + 1) → α) :
    ∏ j : Fin (n + 1), M ((Fin.cons y v : Fin (n + 2) → α) j.succ)
      ((Fin.cons y v : Fin (n + 2) → α) j.castSucc) =
      M (v 0) y * ∏ j : Fin n, M (v j.succ) (v j.castSucc) := by
  rw [Fin.prod_univ_succ]
  try congr 1
  try simp

theorem cons_last (n : ℕ) (y : α) (v : Fin (n + 1) → α) :
    (Fin.cons y v : Fin (n + 2) → α) (Fin.last (n + 1)) = v (Fin.last n) := by
  rw [← Fin.succ_last, Fin.cons_succ]

/-- **The walk formula:** `(Mⁿ)_{ba} = Σ_v [v₀ = a, vₙ = b] Π_j M(v_{j+1}, v_j)`. -/
theorem pow_apply_walks (M : Matrix α α R) (n : ℕ) (a b : α) :
    (M ^ n) b a = ∑ v : Fin (n + 1) → α,
      if v 0 = a ∧ v (Fin.last n) = b then ∏ j : Fin n, M (v j.succ) (v j.castSucc) else 0 := by
  induction n generalizing a with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    rw [← (Equiv.funUnique (Fin 1) α).symm.sum_comp]
    simp only [Equiv.funUnique_symm_apply, Fin.last_zero, Finset.univ_eq_empty,
      Finset.prod_empty]
    rw [Finset.sum_eq_single a]
    · by_cases h : b = a
      · simp [h]
      · simp [h, Ne.symm h]
    · intro x _ hx
      simp [hx]
    · simp
  | succ n ih =>
    have hL : (M ^ (n + 1)) b a = ∑ v : Fin (n + 1) → α,
        if v (Fin.last n) = b then M (v 0) a * ∏ j : Fin n, M (v j.succ) (v j.castSucc)
        else 0 := by
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [ih, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_eq_single (v 0)]
      · by_cases h : v (Fin.last n) = b
        · simp [h, mul_comm]
        · simp [h]
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    have hR : (∑ w : Fin (n + 2) → α, if w 0 = a ∧ w (Fin.last (n + 1)) = b then
          ∏ j : Fin (n + 1), M (w j.succ) (w j.castSucc) else 0) =
        ∑ v : Fin (n + 1) → α,
          if v (Fin.last n) = b then M (v 0) a * ∏ j : Fin n, M (v j.succ) (v j.castSucc)
          else 0 := by
      rw [← (Fin.consEquiv fun _ : Fin (n + 2) => α).sum_comp, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, prod_cons_walk, cons_last]
      rw [Finset.sum_eq_single a]
      · refine Finset.sum_congr rfl fun v _ => ?_
        simp
      · intro y _ hy
        refine Finset.sum_eq_zero fun v _ => ?_
        simp [hy]
      · simp
    rw [hL, hR]

/-- `Tr Mⁿ` as the sum over closed walks. -/
theorem trace_pow_walks (M : Matrix α α R) (n : ℕ) :
    (M ^ n).trace = ∑ v : Fin (n + 1) → α,
      if v (Fin.last n) = v 0 then ∏ j : Fin n, M (v j.succ) (v j.castSucc) else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag, pow_apply_walks]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single (v 0)]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

/-- The weight of a closed word: `Π_j M(c_{j+1}, c_j)`, read cyclically. -/
def cycW (M : Matrix α α R) {r : ℕ} (hr : 0 < r) (c : Fin r → α) : R :=
  ∏ j ∈ Finset.range r, M (ext hr c (j + 1)) (ext hr c j)

theorem snoc_succ_eq_ext {r : ℕ} (hr : 0 < r) (c : Fin r → α) (j : Fin r) :
    (Fin.snoc c (c ⟨0, hr⟩) : Fin (r + 1) → α) j.succ = ext hr c (j + 1) := by
  by_cases hj : (j : ℕ) + 1 < r
  · have e : j.succ = Fin.castSucc ⟨j + 1, hj⟩ := Fin.ext (by simp)
    rw [e, Fin.snoc_castSucc]
    simp only [ext, Nat.mod_eq_of_lt hj]
  · have hj' : (j : ℕ) + 1 = r := by omega
    have e : j.succ = Fin.last r := Fin.ext (by simp [hj'])
    rw [e, Fin.snoc_last]
    simp only [ext]
    congr 1
    apply Fin.ext
    simp [hj']

/-- **`Tr M^r = Σ_{closed words c} Π_j M(c_{j+1}, c_j)`.** -/
theorem trace_pow_eq_sum (M : Matrix α α R) {r : ℕ} (hr : 0 < r) :
    (M ^ r).trace = ∑ c : Fin r → α, cycW M hr c := by
  rw [trace_pow_walks]
  rw [← (Fin.snocEquiv fun _ : Fin (r + 1) => α).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h0 : ∀ y : α, (Fin.snoc c y : Fin (r + 1) → α) 0 = c ⟨0, hr⟩ := by
    intro y
    have e : (0 : Fin (r + 1)) = Fin.castSucc ⟨0, hr⟩ := Fin.ext (by simp)
    rw [e, Fin.snoc_castSucc]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last, h0]
  rw [Finset.sum_eq_single (c ⟨0, hr⟩)]
  · rw [if_pos rfl, cycW, ← Fin.prod_univ_eq_prod_range
      (fun j => M (ext hr c (j + 1)) (ext hr c j)) r]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fin.snoc_castSucc, snoc_succ_eq_ext, ext_lt]
  · intro y _ hy
    simp [hy]
  · simp

/-- A product over `d·q` steps of a `d`-periodic factor. -/
theorem prod_range_per (g : ℕ → R) {d : ℕ} (hg : HasPer g d) (q : ℕ) :
    ∏ j ∈ Finset.range (d * q), g j = (∏ j ∈ Finset.range d, g j) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih, pow_succ]
    congr 1
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [add_comm, mul_comm]
    exact hg.mul q x

/-- **The weight of a power is the power of the weight.** -/
theorem cycW_rep (M : Matrix α α R) {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (hdr : d ∣ r)
    (p : Fin d → α) : cycW M hr (rep hd p r) = (cycW M hd p) ^ (r / d) := by
  rw [cycW, ext_rep hd hr hdr, cycW]
  have hg : HasPer (fun j => M (ext hd p (j + 1)) (ext hd p j)) d := by
    intro n
    simp only
    rw [show n + d + 1 = (n + 1) + d by omega, ext_per hd p, ext_per hd p]
  obtain ⟨q, rfl⟩ := hdr
  rw [Nat.mul_div_cancel_left q hd]
  exact prod_range_per _ hg q

open Classical in
/-- **Every closed walk counted once:** `Tr M^r = Σ_{d ∣ r} Σ_{p primitive, |p| = d} w(p)^{r/d}`. -/
theorem euler_coefficient (M : Matrix α α R) {r : ℕ} (hr : 0 < r) :
    (M ^ r).trace = ∑ d ∈ r.divisors.attach, ∑ p ∈ (Finset.univ.filter fun p : Fin d.1 → α =>
        minPer (Nat.pos_of_mem_divisors d.2) p = d.1),
      (cycW M (Nat.pos_of_mem_divisors d.2) p) ^ (r / d.1) := by
  rw [trace_pow_eq_sum M hr, sum_words hr]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun p _ => ?_
  exact cycW_rep M _ hr (Nat.dvd_of_mem_divisors d.2) p

open Classical in
/-- **The Euler product, coefficient by coefficient:** the coefficient of `u^r` in
`log det(I − uM)⁻¹ = Σ_r u^r Tr M^r / r` is that of `Σ_{p primitive} (1/|p|) Σ_k (u^{|p|} w(p))^k/k`. -/
theorem euler_log_coefficient (M : Matrix α α ℂ) {r : ℕ} (hr : 0 < r) :
    (M ^ r).trace / r = ∑ d ∈ r.divisors.attach, ∑ p ∈ (Finset.univ.filter
        fun p : Fin d.1 → α => minPer (Nat.pos_of_mem_divisors d.2) p = d.1),
      (1 / (d.1 : ℂ)) * ((cycW M (Nat.pos_of_mem_divisors d.2) p) ^ (r / d.1) /
        ((r / d.1 : ℕ) : ℂ)) := by
  rw [euler_coefficient M hr, Finset.sum_div]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hd : 0 < d.1 := Nat.pos_of_mem_divisors d.2
  obtain ⟨q, hq⟩ := Nat.dvd_of_mem_divisors d.2
  have hq' : r / d.1 = q := Nat.div_eq_of_eq_mul_right hd hq
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hq; omega
    · exact h
  rw [hq']
  have hr' : (r : ℂ) = (d.1 : ℂ) * (q : ℂ) := by exact_mod_cast hq
  rw [hr']
  have hd0 : (d.1 : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  field_simp

end Trace

/-! ## Each primitive class has `|p|` rotations of one weight -/

section Rotations

variable {α : Type*} {R : Type*} [CommRing R]

/-- The rotation of a word by `k` letters. -/
def rot {d : ℕ} (hd : 0 < d) (p : Fin d → α) (k : ℕ) : Fin d → α :=
  fun i => p ⟨(i + k) % d, Nat.mod_lt _ hd⟩

theorem ext_rot {d : ℕ} (hd : 0 < d) (p : Fin d → α) (k n : ℕ) :
    ext hd (rot hd p k) n = ext hd p (n + k) := by
  simp only [ext, rot]
  congr 2
  rw [Nat.mod_add_mod]

/-- **The rotations of a primitive word are distinct:** its class has exactly `|p|` members. -/
theorem rot_injective_prim {d : ℕ} (hd : 0 < d) (p : Fin d → α) (hp : minPer hd p = d)
    {k l : ℕ} (hk : k < d) (hl : l < d) (h : rot hd p k = rot hd p l) : k = l := by
  by_contra hne
  wlog hkl : k < l generalizing k l
  · exact this hl hk h.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hkl) (Ne.symm hne))
  have hper : HasPer (ext hd p) (l - k) := by
    intro m
    have h1 := congrFun (congrArg (ext hd) h) (m + d - k)
    rw [ext_rot, ext_rot, show m + d - k + k = m + d by omega,
      show m + d - k + l = m + (l - k) + d by omega, ext_per, ext_per] at h1
    exact h1.symm
  have := minPer_le hd p (by omega) hper
  omega

/-- A product over a window of `d` steps of a `d`-periodic factor does not depend on the window. -/
theorem prod_range_shift (g : ℕ → R) {d : ℕ} (hd : 0 < d) (hg : HasPer g d) (k : ℕ) :
    ∏ j ∈ Finset.range d, g (j + k) = ∏ j ∈ Finset.range d, g j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih]
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [Finset.prod_range_succ (fun j => g (j + (k + 1))),
      Finset.prod_range_succ' (fun j => g (j + k))]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [show j + (k + 1) = j + 1 + k by omega]
    · rw [show d' + (k + 1) = 0 + k + (d' + 1) by omega, hg]

/-- The weight is the same along the class. -/
theorem cycW_rot [Fintype α] [DecidableEq α] (M : Matrix α α R) {d : ℕ} (hd : 0 < d)
    (p : Fin d → α) (k : ℕ) : cycW M hd (rot hd p k) = cycW M hd p := by
  simp only [cycW, ext_rot]
  have hper : HasPer (fun j => M (ext hd p (j + 1)) (ext hd p j)) d := by
    intro n
    simp only
    rw [show n + d + 1 = (n + 1) + d by omega, ext_per hd p, ext_per hd p]
  have e : ∀ j, M (ext hd p (j + 1 + k)) (ext hd p (j + k)) =
      M (ext hd p (j + k + 1)) (ext hd p (j + k)) := by
    intro j
    rw [show j + 1 + k = j + k + 1 by omega]
  rw [Finset.prod_congr rfl (fun j _ => e j)]
  exact prod_range_shift (fun j => M (ext hd p (j + 1)) (ext hd p j)) hd hper k

end Rotations

/-! ## With a connection: the holonomy of each closed walk -/

section Block

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {R : Type*} [CommRing R]

/-- The ordered product `A_{n−1} ⋯ A_0`. -/
def holL (A : ℕ → Matrix ι ι R) : ℕ → Matrix ι ι R
  | 0 => 1
  | n + 1 => A n * holL A n

theorem holL_succ (A : ℕ → Matrix ι ι R) (n : ℕ) : holL A (n + 1) = A n * holL A n := rfl

theorem holL_add (A : ℕ → Matrix ι ι R) (m n : ℕ) :
    holL A (m + n) = holL (fun j => A (m + j)) n * holL A m := by
  induction n with
  | zero => simp [holL]
  | succ n ih => rw [← add_assoc, holL_succ, ih, holL_succ, Matrix.mul_assoc]

/-- **The walk formula for an ordered product.** -/
theorem holL_apply_walks (A : ℕ → Matrix ι ι R) (n : ℕ) (a b : ι) :
    holL A n b a = ∑ v : Fin (n + 1) → ι,
      if v 0 = a ∧ v (Fin.last n) = b then ∏ j : Fin n, A j (v j.succ) (v j.castSucc) else 0 := by
  induction n generalizing b with
  | zero =>
    simp only [holL, Matrix.one_apply]
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    simp only [Equiv.funUnique_symm_apply, Fin.last_zero, Finset.univ_eq_empty,
      Finset.prod_empty]
    rw [Finset.sum_eq_single a]
    · by_cases h : b = a
      · simp [h]
      · simp [h, Ne.symm h]
    · intro x _ hx
      simp [hx]
    · simp
  | succ n ih =>
    have hL : holL A (n + 1) b a = ∑ v : Fin (n + 1) → ι,
        if v 0 = a then A n b (v (Fin.last n)) * ∏ j : Fin n, A j (v j.succ) (v j.castSucc)
        else 0 := by
      rw [holL_succ, Matrix.mul_apply]
      simp_rw [ih, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_eq_single (v (Fin.last n))]
      · by_cases h : v 0 = a
        · simp [h]
        · simp [h]
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    have hR : (∑ w : Fin (n + 2) → ι, if w 0 = a ∧ w (Fin.last (n + 1)) = b then
          ∏ j : Fin (n + 1), A j (w j.succ) (w j.castSucc) else 0) =
        ∑ v : Fin (n + 1) → ι,
          if v 0 = a then A n b (v (Fin.last n)) * ∏ j : Fin n, A j (v j.succ) (v j.castSucc)
          else 0 := by
      rw [← (Fin.snocEquiv fun _ : Fin (n + 2) => ι).sum_comp, Fintype.sum_prod_type,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      have h0 : ∀ y : ι, (Fin.snoc v y : Fin (n + 2) → ι) 0 = v 0 := by
        intro y
        have e : (0 : Fin (n + 2)) = Fin.castSucc 0 := rfl
        rw [e, Fin.snoc_castSucc]
      have hp : ∀ y : ι, ∏ j : Fin (n + 1), A j ((Fin.snoc v y : Fin (n + 2) → ι) j.succ)
          ((Fin.snoc v y : Fin (n + 2) → ι) j.castSucc) =
          (∏ j : Fin n, A j (v j.succ) (v j.castSucc)) * A n y (v (Fin.last n)) := by
        intro y
        rw [Fin.prod_univ_castSucc]
        congr 1
        · refine Finset.prod_congr rfl fun j _ => ?_
          rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
          try rfl
        · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
          try rfl
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last, h0, hp]
      rw [Finset.sum_eq_single b]
      · by_cases h : v 0 = a
        · simp [h, mul_comm]
        · simp [h]
      · intro y _ hy
        simp [hy]
      · simp
    rw [hL, hR]

/-- `Tr (A_{r−1} ⋯ A_0) = Σ_{closed index words i} Π_j (A_j)_{i_{j+1} i_j}`. -/
theorem trace_holL_eq_sum (A : ℕ → Matrix ι ι R) {r : ℕ} (hr : 0 < r) :
    (holL A r).trace = ∑ i : Fin r → ι,
      ∏ j ∈ Finset.range r, A j (ext hr i (j + 1)) (ext hr i j) := by
  have hw : (holL A r).trace = ∑ v : Fin (r + 1) → ι,
      if v (Fin.last r) = v 0 then ∏ j : Fin r, A j (v j.succ) (v j.castSucc) else 0 := by
    rw [Matrix.trace]
    simp only [Matrix.diag, holL_apply_walks]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_eq_single (v 0)]
    · simp
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  rw [hw, ← (Fin.snocEquiv fun _ : Fin (r + 1) => ι).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h0 : ∀ y : ι, (Fin.snoc c y : Fin (r + 1) → ι) 0 = c ⟨0, hr⟩ := by
    intro y
    have e : (0 : Fin (r + 1)) = Fin.castSucc ⟨0, hr⟩ := Fin.ext (by simp)
    rw [e, Fin.snoc_castSucc]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last, h0]
  rw [Finset.sum_eq_single (c ⟨0, hr⟩)]
  · rw [if_pos rfl, ← Fin.prod_univ_eq_prod_range
      (fun j => A j (ext hr c (j + 1)) (ext hr c j)) r]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fin.snoc_castSucc, snoc_succ_eq_ext, ext_lt]
  · intro y _ hy
    simp [hy]
  · simp

/-- The block of `M` from the state `a` to the state `a'`. -/
def blk (M : Matrix (α × ι) (α × ι) R) (a' a : α) : Matrix ι ι R := fun i' i => M (a', i') (a, i)

/-- **The holonomy of a closed walk:** the ordered product of its blocks. -/
def hol (M : Matrix (α × ι) (α × ι) R) {r : ℕ} (hr : 0 < r) (c : Fin r → α) : Matrix ι ι R :=
  holL (fun j => blk M (ext hr c (j + 1)) (ext hr c j)) r

theorem ext_pair {r : ℕ} (hr : 0 < r) (c : Fin r → α) (i : Fin r → ι) (n : ℕ) :
    ext hr (fun j => (c j, i j)) n = (ext hr c n, ext hr i n) := rfl

/-- **`Tr B^r = Σ_{closed histories c} Tr hol(c)`.** -/
theorem trace_pow_block (M : Matrix (α × ι) (α × ι) R) {r : ℕ} (hr : 0 < r) :
    (M ^ r).trace = ∑ c : Fin r → α, (hol M hr c).trace := by
  rw [trace_pow_eq_sum M hr,
    ← (Equiv.arrowProdEquivProdArrow (Fin r) (fun _ => α) (fun _ => ι)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hol, trace_holL_eq_sum _ hr]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

theorem holL_per (A : ℕ → Matrix ι ι R) {d : ℕ} (hA : HasPer A d) (q : ℕ) :
    holL A (d * q) = (holL A d) ^ q := by
  induction q with
  | zero => simp [holL]
  | succ q ih =>
    rw [Nat.mul_succ, holL_add, ih, pow_succ']
    congr 1
    have e : (fun j => A (d * q + j)) = A := by
      funext j
      rw [add_comm, mul_comm]
      exact hA.mul q j
    rw [e]

/-- **The holonomy of a repetition is the power of the holonomy.** -/
theorem hol_rep (M : Matrix (α × ι) (α × ι) R) {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (hdr : d ∣ r) (p : Fin d → α) : hol M hr (rep hd p r) = (hol M hd p) ^ (r / d) := by
  rw [hol, ext_rep hd hr hdr, hol]
  have hA : HasPer (fun j => blk M (ext hd p (j + 1)) (ext hd p j)) d := by
    intro n
    simp only
    rw [show n + d + 1 = (n + 1) + d by omega, ext_per hd p, ext_per hd p]
  obtain ⟨q, rfl⟩ := hdr
  rw [Nat.mul_div_cancel_left q hd]
  exact holL_per _ hA q

open Classical in
/-- **Every closed walk counted once, with its holonomy:**
`Tr B^r = Σ_{d ∣ r} Σ_{ℓ primitive, |ℓ| = d} Tr (hol ℓ)^{r/d}`. -/
theorem euler_holonomy (M : Matrix (α × ι) (α × ι) R) {r : ℕ} (hr : 0 < r) :
    (M ^ r).trace = ∑ d ∈ r.divisors.attach, ∑ p ∈ (Finset.univ.filter fun p : Fin d.1 → α =>
        minPer (Nat.pos_of_mem_divisors d.2) p = d.1),
      ((hol M (Nat.pos_of_mem_divisors d.2) p) ^ (r / d.1)).trace := by
  rw [trace_pow_block M hr, sum_words hr]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun p _ => ?_
  rw [hol_rep M _ hr (Nat.dvd_of_mem_divisors d.2) p]

open Classical in
/-- **The Euler product with holonomy, coefficient by coefficient:** the coefficient of `u^r` in
`log det(I − uB)⁻¹ = Σ_r u^r Tr B^r/r` equals that of
`Σ_{ℓ primitive} (1/|ℓ|) Σ_k u^{k|ℓ|} Tr(hol ℓ)^k / k = −Σ_{[ℓ]} log det(1 − u^{|ℓ|} hol ℓ)`. -/
theorem euler_holonomy_log (M : Matrix (α × ι) (α × ι) ℂ) {r : ℕ} (hr : 0 < r) :
    (M ^ r).trace / r = ∑ d ∈ r.divisors.attach, ∑ p ∈ (Finset.univ.filter
        fun p : Fin d.1 → α => minPer (Nat.pos_of_mem_divisors d.2) p = d.1),
      (1 / (d.1 : ℂ)) * (((hol M (Nat.pos_of_mem_divisors d.2) p) ^ (r / d.1)).trace /
        ((r / d.1 : ℕ) : ℂ)) := by
  rw [euler_holonomy M hr, Finset.sum_div]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hd : 0 < d.1 := Nat.pos_of_mem_divisors d.2
  obtain ⟨q, hq⟩ := Nat.dvd_of_mem_divisors d.2
  have hq' : r / d.1 = q := Nat.div_eq_of_eq_mul_right hd hq
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hq; omega
    · exact h
  rw [hq']
  have hr' : (r : ℂ) = (d.1 : ℂ) * (q : ℂ) := by exact_mod_cast hq
  rw [hr']
  have hd0 : (d.1 : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  field_simp

/-- The trace of the holonomy is the same at every rotation of the walk. -/
theorem trace_hol_rot (M : Matrix (α × ι) (α × ι) R) {d : ℕ} (hd : 0 < d) (p : Fin d → α)
    (k : ℕ) : (hol M hd (rot hd p k)).trace = (hol M hd p).trace := by
  induction k with
  | zero =>
    have : rot hd p 0 = p := by
      funext i
      simp only [rot, add_zero]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt i.2)
    rw [this]
  | succ k ih =>
    rw [← ih]
    set A : ℕ → Matrix ι ι R := fun j => blk M (ext hd (rot hd p k) (j + 1))
      (ext hd (rot hd p k) j) with hA
    have hrot : (fun j => blk M (ext hd (rot hd p (k + 1)) (j + 1)) (ext hd (rot hd p (k + 1)) j))
        = fun j => A (1 + j) := by
      funext j
      simp only [hA, ext_rot]
      rw [show j + 1 + (k + 1) = 1 + j + 1 + k by omega, show j + (k + 1) = 1 + j + k by omega]
    have e1 : ext hd p (d + 1 + k) = ext hd p (1 + k) := by
      rw [show d + 1 + k = (1 + k) + d by omega, ext_per]
    have e2 : ext hd p (d + k) = ext hd p k := by
      rw [show d + k = k + d by omega, ext_per]
    have hper : A d = A 0 := by
      simp only [hA, ext_rot, zero_add, e1, e2]
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    simp only [hol]
    rw [hrot, ← hA]
    have h1' : holL A (d' + 1) = holL (fun j => A (1 + j)) d' * A 0 := by
      rw [Nat.add_comm d' 1, holL_add]
      simp [holL]
    have h2 : holL (fun j => A (1 + j)) (d' + 1) =
        A (1 + d') * holL (fun j => A (1 + j)) d' := holL_succ _ _
    rw [Nat.add_comm d' 1] at hper
    rw [h2, hper, h1', Matrix.trace_mul_comm]

end Block

end Comparison.GroupsContinuumLaw.Euler
