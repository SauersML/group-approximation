import GroupApproximation.GGT.OsinChainLemma

/-!
# Two quasi-elliptic elements with far quasi-fixed points (Osin 2016, Lemma 3.5)

Osin, *Acylindrically hyperbolic groups* (arXiv:1304.1246), Lemma 3.5:

> Let `G` be a group acting on a hyperbolic space `(S, d)`.  Suppose that for some
> `g, h ∈ G` there exist `x, y ∈ S` and `C > 0` such that
> `max{d(x, gx), d(y, hy)} ≤ C` and
> `min{d(x, hx), d(y, gy)} ≥ d(x, y) + 2C + 18δ + 1`.  Then `gh` is a hyperbolic
> isometry.

Osin calls it the hyperbolic analogue of the tree fact that a product of two
elliptic isometries with disjoint fixed sets is loxodromic.  The proof is
Osin's.  The chain `x₀, y₀, x₁, y₁, …` with `xᵢ = (gh)ⁱ x` and `yᵢ = (gh)ⁱ g y`
satisfies the hypothesis of Lemma 2.1.  With the four-point constant the margin
`18δ + 1` becomes any `K > 2δ` (`isLoxodromic_mul_of_quasiFixed`).

## Manuscript status

Infrastructure for Osin's Theorem 1.1 (the limit-set spelling of acylindrical
hyperbolicity used in `sec:torsion-free`); certifies no printed sentence on its
own.
-/

namespace GroupApproximation
namespace GGT
namespace OsinClassification

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **Osin's Remark 2.2**: a far pair of neighbours is a small turn.  If the
outer distance exceeds both legs by `K`, twice the Gromov product at the middle
point plus `K` is at most both legs. -/
theorem two_mul_gromovProduct_add_le {a b c : X} {K : ℝ}
    (hab : dist a b + K ≤ dist a c) (hcb : dist b c + K ≤ dist a c) :
    2 * gromovProduct a c b + K ≤ dist a b ∧
      2 * gromovProduct a c b + K ≤ dist b c := by
  have hcb' : dist c b = dist b c := dist_comm c b
  unfold gromovProduct
  constructor <;> linarith

/-- **A two-periodic chain needs the turn conditions at two vertices only.** -/
theorem chain_turns_of_two_periodic (hiso : IsIsometricAction G X) {g : G} {K : ℝ}
    (z : ℕ → X) (hper : ∀ n : ℕ, z (n + 2) = g • z n)
    (h0 : 2 * gromovProduct (z 0) (z 2) (z 1) + K ≤ dist (z 0) (z 1) ∧
      2 * gromovProduct (z 0) (z 2) (z 1) + K ≤ dist (z 1) (z 2))
    (h1 : 2 * gromovProduct (z 1) (z 3) (z 2) + K ≤ dist (z 1) (z 2) ∧
      2 * gromovProduct (z 1) (z 3) (z 2) + K ≤ dist (z 2) (z 3)) :
    ∀ n : ℕ,
      2 * gromovProduct (z n) (z (n + 2)) (z (n + 1)) + K ≤ dist (z n) (z (n + 1)) ∧
        2 * gromovProduct (z n) (z (n + 2)) (z (n + 1)) + K ≤
          dist (z (n + 1)) (z (n + 2)) := by
  have htr : ∀ m : ℕ,
      (2 * gromovProduct (z m) (z (m + 2)) (z (m + 1)) + K ≤ dist (z m) (z (m + 1)) ∧
        2 * gromovProduct (z m) (z (m + 2)) (z (m + 1)) + K ≤
          dist (z (m + 1)) (z (m + 2))) →
      (2 * gromovProduct (z (m + 1 + 1)) (z (m + 1 + 1 + 2)) (z (m + 1 + 1 + 1)) + K ≤
          dist (z (m + 1 + 1)) (z (m + 1 + 1 + 1)) ∧
        2 * gromovProduct (z (m + 1 + 1)) (z (m + 1 + 1 + 2)) (z (m + 1 + 1 + 1)) + K ≤
          dist (z (m + 1 + 1 + 1)) (z (m + 1 + 1 + 2))) := by
    intro m hm
    have e0 : z (m + 1 + 1) = g • z m := hper m
    have e1 : z (m + 1 + 1 + 1) = g • z (m + 1) := hper (m + 1)
    have e2 : z (m + 1 + 1 + 2) = g • z (m + 2) := hper (m + 2)
    rw [e0, e1, e2, gromovProduct_smul hiso, hiso g (z m) (z (m + 1)),
      hiso g (z (m + 1)) (z (m + 2))]
    exact hm
  have hpair : ∀ n : ℕ,
      (2 * gromovProduct (z n) (z (n + 2)) (z (n + 1)) + K ≤ dist (z n) (z (n + 1)) ∧
        2 * gromovProduct (z n) (z (n + 2)) (z (n + 1)) + K ≤
          dist (z (n + 1)) (z (n + 2))) ∧
      (2 * gromovProduct (z (n + 1)) (z (n + 1 + 2)) (z (n + 1 + 1)) + K ≤
          dist (z (n + 1)) (z (n + 1 + 1)) ∧
        2 * gromovProduct (z (n + 1)) (z (n + 1 + 2)) (z (n + 1 + 1)) + K ≤
          dist (z (n + 1 + 1)) (z (n + 1 + 2))) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih => exact ⟨ih.2, htr n ih.1⟩
  exact fun n => (hpair n).1

/-- **Osin's Lemma 3.5.**  If `g` moves `x` and `h` moves `y` by at most `C`, while
`h` moves `x` and `g` moves `y` by at least `d(x, y) + 2C + K` with `K > 2δ`, then
`gh` is loxodromic. -/
theorem isLoxodromic_mul_of_quasiFixed {δ K C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) (hK : 2 * δ < K) {g h : G} {x y : X}
    (hgx : dist x (g • x) ≤ C) (hhy : dist y (h • y) ≤ C)
    (hhx : dist x y + 2 * C + K ≤ dist x (h • x))
    (hgy : dist x y + 2 * C + K ≤ dist y (g • y)) :
    IsLoxodromic (g * h) x := by
  -- the chain `x, g y, (gh) x, (gh) g y, …`
  let z : ℕ → X := fun n => ((g * h) ^ (n / 2)) • (if n % 2 = 0 then x else g • y)
  have hper : ∀ n : ℕ, z (n + 2) = (g * h) • z n := by
    intro n
    have hdiv : (n + 2) / 2 = n / 2 + 1 := Nat.add_div_right n (by norm_num)
    have hmod : (n + 2) % 2 = n % 2 := Nat.add_mod_right n 2
    show ((g * h) ^ ((n + 2) / 2)) • (if (n + 2) % 2 = 0 then x else g • y) =
      (g * h) • (((g * h) ^ (n / 2)) • (if n % 2 = 0 then x else g • y))
    rw [hdiv, hmod, pow_succ', mul_smul]
  have hz0 : z 0 = x := by simp [z]
  have hz1 : z 1 = g • y := by simp [z]
  have hz2 : z 2 = (g * h) • x := by
    show z (0 + 2) = (g * h) • x
    rw [hper 0, hz0]
  have hz3 : z 3 = (g * h) • g • y := by
    show z (1 + 2) = (g * h) • g • y
    rw [hper 1, hz1]
  -- the four distance estimates of Osin's (19)–(21)
  have hxy : dist x y = dist y x := dist_comm x y
  have hfar_x : dist x y + C + K ≤ dist x ((g * h) • x) := by
    have hiso1 : dist (g • x) ((g * h) • x) = dist x (h • x) := by
      rw [mul_smul, hiso g x (h • x)]
    have htri := dist_triangle (g • x) x ((g * h) • x)
    rw [dist_comm (g • x) x, hiso1] at htri
    linarith
  have hfar_y : dist x y + C + K ≤ dist (g • y) ((g * h) • g • y) := by
    have hiso1 : dist (g • y) ((g * h) • g • y) = dist y (h • g • y) := by
      rw [mul_smul, hiso g y (h • g • y)]
    have hiso2 : dist (h • y) (h • g • y) = dist y (g • y) := hiso h y (g • y)
    have htri := dist_triangle (h • y) y (h • g • y)
    rw [dist_comm (h • y) y, hiso2] at htri
    rw [hiso1]
    linarith
  have hnear_xgy : dist x (g • y) ≤ dist x y + C := by
    have htri := dist_triangle x (g • x) (g • y)
    rw [hiso g x y] at htri
    linarith
  have hnear_gyghx : dist (g • y) ((g * h) • x) ≤ dist x y + C := by
    have hiso1 : dist (g • y) ((g * h) • x) = dist y (h • x) := by
      rw [mul_smul, hiso g y (h • x)]
    have htri := dist_triangle y (h • y) (h • x)
    rw [hiso h y x] at htri
    rw [hiso1]
    linarith
  have hnear_ghx_ghgy : dist ((g * h) • x) ((g * h) • g • y) ≤ dist x y + C := by
    rw [hiso (g * h) x (g • y)]
    exact hnear_xgy
  -- the turn conditions at `g y` and at `(gh) x`
  have h0 := two_mul_gromovProduct_add_le (K := K) (a := x) (b := g • y) (c := (g * h) • x)
    (by linarith) (by linarith)
  have h1 := two_mul_gromovProduct_add_le (K := K) (a := g • y) (b := (g * h) • x)
    (c := (g * h) • g • y) (by linarith) (by linarith)
  have hturns := chain_turns_of_two_periodic hiso z hper
    (by rw [hz0, hz1, hz2]; exact h0) (by rw [hz1, hz2, hz3]; exact h1)
  have hlox := isLoxodromic_of_periodic_chain hδ hK z (p := 2) (by norm_num) hper
    (fun n => (hturns n).1) (fun n => (hturns n).2)
  rwa [hz0] at hlox

end OsinClassification
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.OsinClassification.two_mul_gromovProduct_add_le
#audit_axioms GroupApproximation.GGT.OsinClassification.chain_turns_of_two_periodic
#audit_axioms GroupApproximation.GGT.OsinClassification.isLoxodromic_mul_of_quasiFixed
