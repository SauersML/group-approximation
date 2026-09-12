import GroupApproximation.Algebra.LinearStokesQuadrangle
import GroupApproximation.Meta.AxiomGuard

/-!
# Discrete integrals along short closed polygons and ladders

The Stokes bridge for the hyperbolicity of `GHB(7)` compares the discrete integral
`φ dψ` (`DiscreteStokes.edgeTerm`) along a closed Cayley path with the integral along
a closed chain of sections of coset-complex vertices, and bounds the latter by the
area of a filling disc.  This file proves the metric estimates the comparison uses.

* `abs_sub_le_wordDist_of_lipschitz` (H6): a function moving by at most one along
  every letter of `S` is `1`-Lipschitz for the word metric.
* `abs_polygon_le` (H7): along a closed path of `m` edges whose points lie within `R`
  of a base point in both `φ` and `ψ`, the integral is at most `4 m R²`.  Shifting `φ`
  by the constant `φ p₀` changes the integral by `2 φ(p₀) (ψ(end) − ψ(start))`, which
  vanishes on a closed path.
* `abs_triangle_edgeTerm_le`, `abs_quad_edgeTerm_le`: the triangle and quadrilateral
  cases in a Cayley graph, at `12 M²` and `16 R²`.
* `ladder_identity`, `abs_sub_le_of_closed_rungs`: for two closed paths joined by
  rungs, the difference of the integrals is the sum over the quadrilaterals between
  consecutive rungs.
-/

namespace GroupApproximation
namespace GHBHyperbolicStokes

open WordMetric DiscreteStokes

/-! ## Lipschitz functions and the word metric -/

section Group

variable {Q : Type*} [Group Q] {S : Set Q}

/-- A function moving by at most one along every letter moves by at most the length
along a word. -/
theorem abs_sub_le_length_of_lipschitz {φ : Q → ℤ}
    (hφ : ∀ (g s : Q), s ∈ S → |φ (g * s) - φ g| ≤ 1) :
    ∀ (l : List Q), (∀ x ∈ l, x ∈ S) → ∀ g : Q, |φ (g * l.prod) - φ g| ≤ l.length
  | [], _, g => by simp
  | x :: l, hl, g => by
    have h1 := abs_le.mp (hφ g x (hl x (List.mem_cons.mpr (Or.inl rfl))))
    have h2 := abs_le.mp (abs_sub_le_length_of_lipschitz hφ l
      (fun y hy => hl y (List.mem_cons.mpr (Or.inr hy))) (g * x))
    rw [List.prod_cons, ← mul_assoc, List.length_cons, abs_le]
    push_cast
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **H6.**  A function moving by at most one along every letter of a symmetric
generating set is `1`-Lipschitz for the word metric. -/
theorem abs_sub_le_wordDist_of_lipschitz (hS : IsSymmetricGeneratingSet S) {φ : Q → ℤ}
    (hφ : ∀ (g s : Q), s ∈ S → |φ (g * s) - φ g| ≤ 1) (g h : Q) :
    |φ h - φ g| ≤ wordDist S g h := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS (g⁻¹ * h)
  have key := abs_sub_le_length_of_lipschitz hφ l hl.letters g
  rw [hl.prod_eq, mul_inv_cancel_left, hlen] at key
  exact key

end Group

/-! ## Closed polygons -/

section Polygon

variable {P : Type*}

/-- Shifting `φ` by a constant changes one edge term by `2c` times the change of `ψ`. -/
theorem edgeTerm_sub_const (φ ψ : P → ℤ) (c : ℤ) (g h : P) :
    edgeTerm (fun z => φ z - c) ψ g h = edgeTerm φ ψ g h - 2 * c * (ψ h - ψ g) := by
  simp only [edgeTerm]
  ring

/-- Shifting `φ` by a constant changes the integral along a path by the endpoint term. -/
theorem zipWith_edgeTerm_sub_const (φ ψ : P → ℤ) (c : ℤ) :
    ∀ (x : P) (t : List P),
      (List.zipWith (edgeTerm φ ψ) (x :: t) t).sum =
        (List.zipWith (edgeTerm (fun z => φ z - c) ψ) (x :: t) t).sum +
          2 * c * (ψ ((x :: t).getLast (List.cons_ne_nil x t)) - ψ x)
  | x, [] => by simp
  | x, y :: t => by
    have ih := zipWith_edgeTerm_sub_const φ ψ c y t
    simp only [List.zipWith_cons_cons, List.sum_cons, List.getLast_cons_cons]
    rw [ih, edgeTerm_sub_const φ ψ c x y]
    ring

/-- Along a path whose points satisfy `|φ| ≤ A` and `|ψ − ψ p₀| ≤ B`, each edge term is
at most `2A · 2B`. -/
theorem abs_zipWith_edgeTerm_le (φ ψ : P → ℤ) (p₀ : P) (A B : ℤ) :
    ∀ (x : P) (t : List P), (∀ z ∈ x :: t, |φ z| ≤ A) → (∀ z ∈ x :: t, |ψ z - ψ p₀| ≤ B) →
      |(List.zipWith (edgeTerm φ ψ) (x :: t) t).sum| ≤ t.length * (2 * A * (2 * B))
  | x, [], _, _ => by simp
  | x, y :: t, hA, hB => by
    have ih := abs_zipWith_edgeTerm_le φ ψ p₀ A B y t
      (fun z hz => hA z (List.mem_cons.mpr (Or.inr hz)))
      (fun z hz => hB z (List.mem_cons.mpr (Or.inr hz)))
    have hx := abs_le.mp (hA x (List.mem_cons.mpr (Or.inl rfl)))
    have hy := abs_le.mp (hA y (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
    have hx' := abs_le.mp (hB x (List.mem_cons.mpr (Or.inl rfl)))
    have hy' := abs_le.mp (hB y (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
    have h1 : |φ x + φ y| ≤ 2 * A :=
      abs_le.mpr ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
    have h2 : |ψ y - ψ x| ≤ 2 * B :=
      abs_le.mpr ⟨by linarith [hx'.2, hy'.1], by linarith [hx'.1, hy'.2]⟩
    have hA0 : 0 ≤ 2 * A := by linarith [hx.1, hx.2]
    have hterm : |edgeTerm φ ψ x y| ≤ 2 * A * (2 * B) := by
      unfold edgeTerm
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hA0
    simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons]
    have hsum := abs_add_le (edgeTerm φ ψ x y) (List.zipWith (edgeTerm φ ψ) (y :: t) t).sum
    push_cast
    linarith [hsum, hterm, ih]

/-- **H7.**  Along a closed path of `t.length` edges whose points lie within `R` of `p₀`
in both `φ` and `ψ`, the integral of `φ dψ` is at most `4 R²` per edge. -/
theorem abs_polygon_le (φ ψ : P → ℤ) (p₀ : P) (R : ℤ) (x : P) (t : List P)
    (hclosed : (x :: t).getLast (List.cons_ne_nil x t) = x)
    (hφ : ∀ z ∈ x :: t, |φ z - φ p₀| ≤ R) (hψ : ∀ z ∈ x :: t, |ψ z - ψ p₀| ≤ R) :
    |(List.zipWith (edgeTerm φ ψ) (x :: t) t).sum| ≤ t.length * (4 * R ^ 2) := by
  rw [zipWith_edgeTerm_sub_const φ ψ (φ p₀) x t, hclosed, sub_self, mul_zero, add_zero]
  have h := abs_zipWith_edgeTerm_le (fun z => φ z - φ p₀) ψ p₀ R R x t hφ hψ
  calc _ ≤ (t.length : ℤ) * (2 * R * (2 * R)) := h
    _ = t.length * (4 * R ^ 2) := by ring

end Polygon

/-! ## Triangles and quadrilaterals in a Cayley graph -/

section Cayley

variable {Q : Type*} [Group Q] {S : Set Q}

/-- Points within `M` of `p` stay within `M` of `p` in a Lipschitz function. -/
theorem abs_sub_le_of_mem_ball (hS : IsSymmetricGeneratingSet S) {χ : Q → ℤ}
    (hχ : ∀ (g s : Q), s ∈ S → |χ (g * s) - χ g| ≤ 1) {M : ℕ} {p : Q} {l : List Q}
    (hl : ∀ z ∈ l, wordDist S p z ≤ M) : ∀ z ∈ l, |χ z - χ p| ≤ (M : ℤ) := by
  intro z hz
  exact (abs_sub_le_wordDist_of_lipschitz hS hχ p z).trans (by exact_mod_cast hl z hz)

/-- **The triangle bound**: a triangle whose vertices lie within `M` of its first vertex
has integral at most `12 M²`. -/
theorem abs_triangle_edgeTerm_le (hS : IsSymmetricGeneratingSet S) {φ ψ : Q → ℤ}
    (hφ : ∀ (g s : Q), s ∈ S → |φ (g * s) - φ g| ≤ 1)
    (hψ : ∀ (g s : Q), s ∈ S → |ψ (g * s) - ψ g| ≤ 1) {M : ℕ} {p q r : Q}
    (hpq : wordDist S p q ≤ M) (hpr : wordDist S p r ≤ M) :
    |edgeTerm φ ψ p q + edgeTerm φ ψ q r + edgeTerm φ ψ r p| ≤ 12 * (M : ℤ) ^ 2 := by
  have hball : ∀ z ∈ [p, q, r, p], wordDist S p z ≤ M := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with h | h | h | h <;> rw [h]
    · rw [wordDist_self]
      exact Nat.zero_le M
    · exact hpq
    · exact hpr
    · rw [wordDist_self]
      exact Nat.zero_le M
  have h := abs_polygon_le φ ψ p M p [q, r, p] rfl
    (abs_sub_le_of_mem_ball hS hφ hball) (abs_sub_le_of_mem_ball hS hψ hball)
  have hsum : (List.zipWith (edgeTerm φ ψ) [p, q, r, p] [q, r, p]).sum =
      edgeTerm φ ψ p q + edgeTerm φ ψ q r + edgeTerm φ ψ r p := by
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil]
    ring
  have hlen : (([q, r, p] : List Q).length : ℤ) = 3 := rfl
  rw [hsum, hlen] at h
  calc _ ≤ (3 : ℤ) * (4 * (M : ℤ) ^ 2) := h
    _ = 12 * (M : ℤ) ^ 2 := by ring

/-- **The quadrilateral bound**: a quadrilateral `g → g' → h' → h → g` whose vertices lie
within `R` of `g` has integral at most `16 R²`. -/
theorem abs_quad_edgeTerm_le (hS : IsSymmetricGeneratingSet S) {φ ψ : Q → ℤ}
    (hφ : ∀ (g s : Q), s ∈ S → |φ (g * s) - φ g| ≤ 1)
    (hψ : ∀ (g s : Q), s ∈ S → |ψ (g * s) - ψ g| ≤ 1) {R : ℕ} {g g' h h' : Q}
    (hg' : wordDist S g g' ≤ R) (hh' : wordDist S g h' ≤ R) (hh : wordDist S g h ≤ R) :
    |edgeTerm φ ψ g g' + edgeTerm φ ψ g' h' + edgeTerm φ ψ h' h + edgeTerm φ ψ h g| ≤
      16 * (R : ℤ) ^ 2 := by
  have hball : ∀ z ∈ [g, g', h', h, g], wordDist S g z ≤ R := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with e | e | e | e | e <;> rw [e]
    · rw [wordDist_self]
      exact Nat.zero_le R
    · exact hg'
    · exact hh'
    · exact hh
    · rw [wordDist_self]
      exact Nat.zero_le R
  have hp := abs_polygon_le φ ψ g R g [g', h', h, g] rfl
    (abs_sub_le_of_mem_ball hS hφ hball) (abs_sub_le_of_mem_ball hS hψ hball)
  have hsum : (List.zipWith (edgeTerm φ ψ) [g, g', h', h, g] [g', h', h, g]).sum =
      edgeTerm φ ψ g g' + edgeTerm φ ψ g' h' + edgeTerm φ ψ h' h + edgeTerm φ ψ h g := by
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil]
    ring
  have hlen : (([g', h', h, g] : List Q).length : ℤ) = 4 := rfl
  rw [hsum, hlen] at hp
  calc _ ≤ (4 : ℤ) * (4 * (R : ℤ) ^ 2) := hp
    _ = 16 * (R : ℤ) ^ 2 := by ring

end Cayley

/-! ## Ladders -/

section Ladder

variable {P : Type*}

/-- The integral around the quadrilateral between the rungs `u` and `v`:
`u.1 → v.1 → v.2 → u.2 → u.1`. -/
def quadTerm (φ ψ : P → ℤ) (u v : P × P) : ℤ :=
  edgeTerm φ ψ u.1 v.1 + edgeTerm φ ψ v.1 v.2 + edgeTerm φ ψ v.2 u.2 + edgeTerm φ ψ u.2 u.1

/-- **The ladder identity.**  For a list of rungs `(gₖ, hₖ)`, the integral along the
`g`-path minus the integral along the `h`-path is the sum of the quadrilateral terms plus
the rung term at the start minus the rung term at the end. -/
theorem ladder_identity (φ ψ : P → ℤ) :
    ∀ (x : P × P) (t : List (P × P)),
      (List.zipWith (edgeTerm φ ψ) (x.1 :: t.map Prod.fst) (t.map Prod.fst)).sum -
          (List.zipWith (edgeTerm φ ψ) (x.2 :: t.map Prod.snd) (t.map Prod.snd)).sum =
        (List.zipWith (quadTerm φ ψ) (x :: t) t).sum + edgeTerm φ ψ x.1 x.2 -
          edgeTerm φ ψ ((x :: t).getLast (List.cons_ne_nil x t)).1
            ((x :: t).getLast (List.cons_ne_nil x t)).2
  | x, [] => by simp
  | x, y :: t => by
    have ih := ladder_identity φ ψ y t
    have h1 := edgeTerm_swap φ ψ x.2 y.2
    have h2 := edgeTerm_swap φ ψ x.1 x.2
    have hq : quadTerm φ ψ x y = edgeTerm φ ψ x.1 y.1 + edgeTerm φ ψ y.1 y.2 +
        edgeTerm φ ψ y.2 x.2 + edgeTerm φ ψ x.2 x.1 := rfl
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, List.getLast_cons_cons]
    linarith [ih, h1, h2, hq]

/-- A sum over consecutive pairs of a chain along which every term is at most `C`. -/
theorem abs_sum_zipWith_le {α : Type*} (f : α → α → ℤ) (C : ℤ) :
    ∀ (x : α) (t : List α), List.IsChain (fun u v => |f u v| ≤ C) (x :: t) →
      |(List.zipWith f (x :: t) t).sum| ≤ t.length * C
  | x, [], _ => by simp
  | x, y :: t, h => by
    rw [List.isChain_cons_cons] at h
    have h1 : |f x y| ≤ C := h.1
    have ih := abs_sum_zipWith_le f C y t h.2
    simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons]
    have hsum := abs_add_le (f x y) (List.zipWith f (y :: t) t).sum
    push_cast
    linarith [hsum, h1, ih]

/-- **Closed ladders.**  If the first and last rungs agree and every quadrilateral term is
at most `C`, the integrals along the two closed paths differ by at most `C` per step. -/
theorem abs_sub_le_of_closed_rungs (φ ψ : P → ℤ) (C : ℤ) (x : P × P) (t : List (P × P))
    (hclosed : (x :: t).getLast (List.cons_ne_nil x t) = x)
    (hquad : List.IsChain (fun u v => |quadTerm φ ψ u v| ≤ C) (x :: t)) :
    |(List.zipWith (edgeTerm φ ψ) (x.1 :: t.map Prod.fst) (t.map Prod.fst)).sum -
        (List.zipWith (edgeTerm φ ψ) (x.2 :: t.map Prod.snd) (t.map Prod.snd)).sum| ≤
      t.length * C := by
  rw [ladder_identity φ ψ x t, hclosed, add_sub_cancel_right]
  exact abs_sum_zipWith_le (quadTerm φ ψ) C x t hquad

end Ladder

end GHBHyperbolicStokes
end GroupApproximation

#audit_axioms GroupApproximation.GHBHyperbolicStokes.abs_sub_le_wordDist_of_lipschitz
#audit_axioms GroupApproximation.GHBHyperbolicStokes.abs_polygon_le
#audit_axioms GroupApproximation.GHBHyperbolicStokes.abs_triangle_edgeTerm_le
#audit_axioms GroupApproximation.GHBHyperbolicStokes.abs_quad_edgeTerm_le
#audit_axioms GroupApproximation.GHBHyperbolicStokes.ladder_identity
#audit_axioms GroupApproximation.GHBHyperbolicStokes.abs_sub_le_of_closed_rungs
