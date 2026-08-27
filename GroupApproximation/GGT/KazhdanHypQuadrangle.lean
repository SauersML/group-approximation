import GroupApproximation.GGT.KazhdanHypPolygonal

/-!
# The rational link certificate for generalized-quadrangle links

`GGT/KazhdanHypLinkGap.lean` builds the rational Gram factor of
`L/d - gap * P0` when the link is the incidence graph of a projective plane.
That case is Euclidean: triangles with girth-`6` links give `1/3 + 1/6 = 1/2`,
the `A~_2` tiling, and the resulting groups are Kazhdan but not hyperbolic.

This module does the girth-`8` case, where `1/3 + 1/8 = 11/24 < 1/2` and the
complex is `CAT(-1)`.  The link is the incidence graph of a generalized
quadrangle of order `(q,q)`, and the two-step count is no longer
`q * delta + [same side]`: it is

```
    A² = (q+1) I + C ,
```

with `C` the **collinearity** graph --- collinear points on the point side,
concurrent lines on the line side, zero across.  `C` is not a projector, so the
single completed square of the projective-plane case does not close.  What
closes it is that `C` is strongly regular.

## Two completed squares

The point graph of `GQ(q,q)` is strongly regular with parameters
`((q+1)(q²+1), q(q+1), q-1, q+1)`, so `C² = (k-μ)I + (λ-μ)C + μ J'` reads

```
    C² = (q²-1) I - 2 C + (q+1) J' ,
```

`J'` the same-side all-ones matrix.  Completing the square at the **integer**
shift `q-1` gives, exactly,

```
    (C - (q-1) I)² = 2q [ (q-1) I - C ] + (q+1) J' ,
```

so off the constants `C ⪯ (q-1) I`, with an explicit rational square and no
eigenvalue estimate.  Feeding that into `A² = (q+1)I + C` gives `A² ⪯ 2q I`
there, which is what `√(2q)` means, and the second completed square

```
    (A - μ I)² ⪰ 0   ⟹   A ⪯ ((2q + μ²)/(2μ)) I
```

finishes the certificate with `gap = 1 - (2q + μ²)/(2μ(q+1))`.  The threshold
`gap > 1/2` is exactly `μ² - μ(q+1) + 2q < 0`, which has a rational solution
precisely when `(q+1)² > 8q`, that is `q ≥ 7`; and at `q = 8` one may take the
integer `μ = 4`, giving `gap = 5/9`.  No square root appears anywhere.

## The shape of the factor

Writing `P_W` for the projection off the constant vector and off the
bipartition sign, and `B_X = P_W (X - ν I)`, the identity proved below is

```
    L/d - gap P0  =  (1/(2μd)) B_A²  +  (1/(4μdq)) B_C²  +  ((1+s)/n) w wᵀ ,
```

with `d = q+1`, `s = 1 - gap`, `n = 2(q+1)(q²+1)`.  The `C` coefficients of the
first two blocks cancel --- `1/(2μd)` against `-2q/(4μdq)` --- which is the
whole reason two squares suffice, and the `J` and `w wᵀ` coefficients match on
the nose once `n = 2(q+1)(q²+1)`, the point count of the quadrangle.

`sum_projSquare` is the one lemma both blocks use: for any symmetric `X` with
`X · 1 = ξ · 1` and `X · w = η · w`, the projected square `B_X = P_W(X - νI)`
satisfies

```
    (B_X²)(v,v') = Sq(v,v') - 2ν X(v,v') + ν² δ(v,v') - (ξ-ν)²/n - ((η-ν)²/n) σ ,
```

where `Sq = X²` and `σ = sign v * sign v'`.  Applying it at `(X,ν,ξ,η) = (A,μ,d,-d)`
and at `(C, q-1, k, k)` is the whole computation.

## What this does not supply

A triangle table.  The literature has one-vertex triangular presentations with
`GQ(2,2)` links --- Kangaslampi and Vdovina classify them, `15` generators and
`15` relators `x_i x_j x_k = 1`, `23` torsion-free and `168` torsion groups ---
and `GQ(2,2)` has `kappa = 1/3`, below the threshold.  No construction at any
order `q ≥ 7` is recorded in the sources consulted.  `GGT/KazhdanHypPolygonal.lean`
carries that gap as `GQEightTableExists`.
-/

namespace GroupApproximation
namespace KazhdanHyp

universe u

/-! ## Finite sum helpers -/

private theorem qsum_kron_mul {α : Type u} [Fintype α] [DecidableEq α]
    (f : α → ℚ) (v : α) :
    ∑ u, (if u = v then (1 : ℚ) else 0) * f u = f v := by
  classical
  simp

private theorem qsum_mul_kron {α : Type u} [Fintype α] [DecidableEq α]
    (f : α → ℚ) (v : α) :
    ∑ u, f u * (if u = v then (1 : ℚ) else 0) = f v := by
  classical
  simp

private theorem qsum_kron_kron {α : Type u} [Fintype α] [DecidableEq α] (v v' : α) :
    ∑ u : α, (if u = v then (1 : ℚ) else 0) * (if u = v' then (1 : ℚ) else 0)
      = if v = v' then 1 else 0 :=
  qsum_kron_mul (fun u => if u = v' then (1 : ℚ) else 0) v

private theorem qsum_kron {α : Type u} [Fintype α] [DecidableEq α] (v : α) :
    ∑ u : α, (if u = v then (1 : ℚ) else 0) = 1 := by
  classical
  simp

private theorem qsum_one {α : Type u} [Fintype α] :
    ∑ _u : α, (1 : ℚ) = (Fintype.card α : ℚ) := by
  simp

/-! ## The projected square

One lemma, applied twice: once to the incidence table and once to the
collinearity table. -/

/-- **The projected completed square, evaluated.**  For a symmetric table `X`
whose columns sum to `xi` and which sends the bipartition sign to `eta` times
itself, the column of `P_W (X - nu)` has Gram

```
    Sq - 2 nu X + nu² delta - (xi-nu)²/n - ((eta-nu)²/n) sign sign ,
```

where `Sq` is the two-step table of `X` and `n` the vertex count.  The two
correction coefficients `(xi-nu)/n` and `(eta-nu)/n` are exactly the ones that
make the column annihilate the constant vector and the sign vector. -/
theorem sum_projSquare {V : Type u} [Fintype V] [DecidableEq V]
    (X Sq : V → V → ℚ) (sign : V → ℚ) (xi eta nu : ℚ)
    (hcard : ((Fintype.card V : ℕ) : ℚ) ≠ 0)
    (hsymm : ∀ u v, X u v = X v u)
    (hsignsq : ∀ u, sign u * sign u = 1)
    (hsignsum : ∑ u, sign u = 0)
    (hcolsum : ∀ v, ∑ u, X u v = xi)
    (hsigncol : ∀ v, ∑ u, X u v * sign u = eta * sign v)
    (hsq : ∀ v v', ∑ u, X u v * X u v' = Sq v v')
    (v v' : V) :
    ∑ u, (X u v - nu * (if u = v then 1 else 0)
            - (xi - nu) / (Fintype.card V : ℚ)
            - ((eta - nu) / (Fintype.card V : ℚ)) * (sign u * sign v))
        * (X u v' - nu * (if u = v' then 1 else 0)
            - (xi - nu) / (Fintype.card V : ℚ)
            - ((eta - nu) / (Fintype.card V : ℚ)) * (sign u * sign v'))
      = Sq v v' - 2 * nu * X v v' + nu ^ 2 * (if v = v' then 1 else 0)
        - (xi - nu) ^ 2 / (Fintype.card V : ℚ)
        - ((eta - nu) ^ 2 / (Fintype.card V : ℚ)) * (sign v * sign v') := by
  classical
  have e1 : ∑ u, X u v * X u v' = Sq v v' := hsq v v'
  have e2 : ∑ u, (if u = v then (1 : ℚ) else 0) * X u v' = X v v' :=
    qsum_kron_mul (fun u => X u v') v
  have e3 : ∑ u, X u v * (if u = v' then (1 : ℚ) else 0) = X v v' := by
    have h : ∑ u, X u v * (if u = v' then (1 : ℚ) else 0) = X v' v :=
      qsum_mul_kron (fun u => X u v) v'
    rw [h]
    exact hsymm v' v
  have e4 : ∑ u : V, (if u = v then (1 : ℚ) else 0) * (if u = v' then (1 : ℚ) else 0)
      = if v = v' then 1 else 0 := qsum_kron_kron v v'
  have e5 : ∑ u, X u v' = xi := hcolsum v'
  have e6 : ∑ u, X u v = xi := hcolsum v
  have e7 : ∑ u : V, (if u = v then (1 : ℚ) else 0) = 1 := qsum_kron v
  have e8 : ∑ u : V, (if u = v' then (1 : ℚ) else 0) = 1 := qsum_kron v'
  have e9 : ∑ _u : V, (1 : ℚ) = (Fintype.card V : ℚ) := qsum_one
  have e10 : ∑ u, X u v * sign u = eta * sign v := hsigncol v
  have e11 : ∑ u, X u v' * sign u = eta * sign v' := hsigncol v'
  have e12 : ∑ u, (if u = v then (1 : ℚ) else 0) * sign u = sign v :=
    qsum_kron_mul sign v
  have e13 : ∑ u, (if u = v' then (1 : ℚ) else 0) * sign u = sign v' :=
    qsum_kron_mul sign v'
  have e14 : ∑ u, sign u = 0 := hsignsum
  have e15 : ∑ u : V, sign u * sign u = (Fintype.card V : ℚ) := by
    rw [show (∑ u : V, sign u * sign u) = ∑ _u : V, (1 : ℚ) from
      Finset.sum_congr rfl fun u _ => hsignsq u]
    exact qsum_one
  have key : ∑ u, (X u v - nu * (if u = v then 1 else 0)
            - (xi - nu) / (Fintype.card V : ℚ)
            - ((eta - nu) / (Fintype.card V : ℚ)) * (sign u * sign v))
        * (X u v' - nu * (if u = v' then 1 else 0)
            - (xi - nu) / (Fintype.card V : ℚ)
            - ((eta - nu) / (Fintype.card V : ℚ)) * (sign u * sign v'))
      = (∑ u, X u v * X u v')
        - nu * (∑ u, (if u = v then (1 : ℚ) else 0) * X u v')
        - nu * (∑ u, X u v * (if u = v' then (1 : ℚ) else 0))
        + nu ^ 2 *
            (∑ u : V, (if u = v then (1 : ℚ) else 0) * (if u = v' then (1 : ℚ) else 0))
        - ((xi - nu) / (Fintype.card V : ℚ)) * (∑ u, X u v')
        - ((xi - nu) / (Fintype.card V : ℚ)) * (∑ u, X u v)
        + ((xi - nu) / (Fintype.card V : ℚ)) * nu *
            (∑ u : V, (if u = v then (1 : ℚ) else 0))
        + ((xi - nu) / (Fintype.card V : ℚ)) * nu *
            (∑ u : V, (if u = v' then (1 : ℚ) else 0))
        + ((xi - nu) / (Fintype.card V : ℚ)) ^ 2 * (∑ _u : V, (1 : ℚ))
        - ((eta - nu) / (Fintype.card V : ℚ)) * sign v' * (∑ u, X u v * sign u)
        - ((eta - nu) / (Fintype.card V : ℚ)) * sign v * (∑ u, X u v' * sign u)
        + ((eta - nu) / (Fintype.card V : ℚ)) * nu * sign v' *
            (∑ u, (if u = v then (1 : ℚ) else 0) * sign u)
        + ((eta - nu) / (Fintype.card V : ℚ)) * nu * sign v *
            (∑ u, (if u = v' then (1 : ℚ) else 0) * sign u)
        + ((xi - nu) / (Fintype.card V : ℚ)) *
            ((eta - nu) / (Fintype.card V : ℚ)) * sign v * (∑ u, sign u)
        + ((xi - nu) / (Fintype.card V : ℚ)) *
            ((eta - nu) / (Fintype.card V : ℚ)) * sign v' * (∑ u, sign u)
        + ((eta - nu) / (Fintype.card V : ℚ)) ^ 2 * sign v * sign v' *
            (∑ u : V, sign u * sign u) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [key, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  have hc : ((Fintype.card V : ℕ) : ℚ) ≠ 0 := hcard
  field_simp
  ring

/-! ## Quadrangle link data -/

/-- **The link of a triangular complex whose vertex links are the incidence
graph of a generalized quadrangle of order `(q,q)`.**

`adj` is the incidence table, `col` the collinearity table --- collinear points,
concurrent lines, zero across sides.  The two square identities are
`A² = (q+1) I + C` and the strong regularity of `C`; `card_eq` is the point
count `(q+1)(q²+1)` doubled.  `mu_bound` is Zuk's threshold in the square-root
free form, and it is solvable exactly when `(q+1)² > 8q`. -/
structure QuadrangleLinkData (V : Type u) [Fintype V] [DecidableEq V] where
  /-- The incidence table of the link. -/
  adj : V → V → ℚ
  /-- The collinearity table: collinear points, concurrent lines, zero across. -/
  col : V → V → ℚ
  /-- The bipartition sign, valued in `±1`. -/
  sign : V → ℚ
  /-- The order `q` of the quadrangle. -/
  ord : ℚ
  /-- The rational shift completing the square for the incidence table. -/
  mu : ℚ
  /-- The incidence table is symmetric. -/
  adj_symm : ∀ u v, adj u v = adj v u
  /-- The collinearity table is symmetric. -/
  col_symm : ∀ u v, col u v = col v u
  /-- The sign is valued in `±1`. -/
  sign_sq : ∀ u, sign u * sign u = 1
  /-- The two sides have equal size. -/
  sign_sum : ∑ u, sign u = 0
  /-- Every point is on `q+1` lines and every line carries `q+1` points. -/
  adj_col_sum : ∀ v, ∑ u, adj u v = ord + 1
  /-- The incidence graph is bipartite. -/
  adj_sign : ∀ v, ∑ u, adj u v * sign u = -(ord + 1) * sign v
  /-- The collinearity graph is `q(q+1)`-regular. -/
  col_col_sum : ∀ v, ∑ u, col u v = ord * (ord + 1)
  /-- The collinearity graph does not mix the two sides. -/
  col_sign : ∀ v, ∑ u, col u v * sign u = ord * (ord + 1) * sign v
  /-- **`A² = (q+1) I + C`**: two vertices on opposite sides have no common
  neighbour, two distinct collinear points have exactly one. -/
  adj_square : ∀ v v', ∑ u, adj u v * adj u v'
      = (ord + 1) * (if v = v' then 1 else 0) + col v v'
  /-- **The collinearity graph is strongly regular** with parameters
  `((q+1)(q²+1), q(q+1), q-1, q+1)`. -/
  col_square : ∀ v v', ∑ u, col u v * col u v'
      = (ord ^ 2 - 1) * (if v = v' then 1 else 0) - 2 * col v v'
        + ((ord + 1) / 2) * (1 + sign v * sign v')
  /-- The vertex count: twice the point count of the quadrangle. -/
  card_eq : ((Fintype.card V : ℕ) : ℚ) = 2 * (ord + 1) * (ord ^ 2 + 1)
  /-- The order is positive. -/
  ord_pos : 0 < ord
  /-- The shift is positive. -/
  mu_pos : 0 < mu
  /-- **Zuk's threshold**, square-root free.  Solvable in `mu` exactly when
  `(q+1)² > 8q`, that is `q ≥ 7`. -/
  mu_bound : mu ^ 2 - mu * (ord + 1) + 2 * ord < 0

namespace QuadrangleLinkData

variable {V : Type u} [Fintype V] [DecidableEq V] (D : QuadrangleLinkData V)

/-- The link degree `q + 1`. -/
def deg : ℚ := D.ord + 1

theorem deg_pos : 0 < D.deg := by
  unfold deg
  linarith [D.ord_pos]

theorem deg_ne_zero : D.deg ≠ 0 := ne_of_gt D.deg_pos

theorem ord_ne_zero : D.ord ≠ 0 := ne_of_gt D.ord_pos

theorem mu_ne_zero : D.mu ≠ 0 := ne_of_gt D.mu_pos

theorem card_pos : (0 : ℚ) < ((Fintype.card V : ℕ) : ℚ) := by
  rw [D.card_eq]
  have h := D.ord_pos
  nlinarith [sq_nonneg D.ord]

theorem card_ne_zero : ((Fintype.card V : ℕ) : ℚ) ≠ 0 := ne_of_gt D.card_pos

/-- The contraction constant `s = (2q + mu²)/(2 mu (q+1))`, which is `1 - gap`. -/
def contraction : ℚ := (2 * D.ord + D.mu ^ 2) / (2 * D.mu * D.deg)

/-- **The link gap.**  At `q = 8` with `mu = 4` this is `1 - 32/72 = 5/9`. -/
def gapValue : ℚ := 1 - D.contraction

/-- **The gap clears Zuk's threshold.**  This is `mu² - mu(q+1) + 2q < 0`
restated. -/
theorem gapValue_gt_half : (1 : ℚ) / 2 < D.gapValue := by
  have hden : (0 : ℚ) < 2 * D.mu * D.deg := by
    have := D.mu_pos
    have := D.deg_pos
    positivity
  have h : D.contraction < 1 / 2 := by
    unfold contraction
    rw [div_lt_iff₀ hden]
    have hb := D.mu_bound
    unfold deg
    nlinarith [hb]
  unfold gapValue
  linarith

/-- The rank-one weight carried by the bipartition sign. -/
def wCoeff : ℚ := (1 + D.contraction) / ((Fintype.card V : ℕ) : ℚ)

theorem contraction_pos : 0 < D.contraction := by
  unfold contraction
  have hnum : (0 : ℚ) < 2 * D.ord + D.mu ^ 2 := by
    have := D.ord_pos
    nlinarith [sq_nonneg D.mu]
  have hden : (0 : ℚ) < 2 * D.mu * D.deg := by
    have := D.mu_pos
    have := D.deg_pos
    positivity
  exact div_pos hnum hden

theorem wCoeff_nonneg : 0 ≤ D.wCoeff := by
  have h := D.contraction_pos
  exact div_nonneg (by linarith) (le_of_lt D.card_pos)

/-- The coefficient of the incidence block: `1/(2 mu (q+1))`. -/
def coeffA : ℚ := 1 / (2 * D.mu * D.deg)

/-- The coefficient of the collinearity block: `1/(4 mu (q+1) q)`. -/
def coeffC : ℚ := 1 / (4 * D.mu * D.deg * D.ord)

theorem coeffA_nonneg : 0 ≤ D.coeffA := by
  unfold coeffA
  have hden : (0 : ℚ) < 2 * D.mu * D.deg := by
    have := D.mu_pos
    have := D.deg_pos
    positivity
  positivity

theorem coeffC_nonneg : 0 ≤ D.coeffC := by
  unfold coeffC
  have hden : (0 : ℚ) < 4 * D.mu * D.deg * D.ord := by
    have := D.mu_pos
    have := D.deg_pos
    have := D.ord_pos
    positivity
  positivity

/-! ### The two projected columns -/

/-- The projected column of the incidence table, at shift `mu`. -/
def colA (u v : V) : ℚ :=
  D.adj u v - D.mu * (if u = v then 1 else 0)
    - (D.deg - D.mu) / ((Fintype.card V : ℕ) : ℚ)
    - ((-D.deg - D.mu) / ((Fintype.card V : ℕ) : ℚ)) * (D.sign u * D.sign v)

/-- The projected column of the collinearity table, at the integer shift
`q - 1`. -/
def colC (u v : V) : ℚ :=
  D.col u v - (D.ord - 1) * (if u = v then 1 else 0)
    - (D.ord * D.deg - (D.ord - 1)) / ((Fintype.card V : ℕ) : ℚ)
    - ((D.ord * D.deg - (D.ord - 1)) / ((Fintype.card V : ℕ) : ℚ)) *
        (D.sign u * D.sign v)

/-- **The incidence block, evaluated**, by `sum_projSquare` at
`(X, nu, xi, eta) = (adj, mu, q+1, -(q+1))`. -/
theorem sum_colA (v v' : V) :
    ∑ u, D.colA u v * D.colA u v'
      = ((D.deg * (if v = v' then 1 else 0) + D.col v v')
          - 2 * D.mu * D.adj v v' + D.mu ^ 2 * (if v = v' then 1 else 0)
          - (D.deg - D.mu) ^ 2 / ((Fintype.card V : ℕ) : ℚ)
          - ((-D.deg - D.mu) ^ 2 / ((Fintype.card V : ℕ) : ℚ))
              * (D.sign v * D.sign v')) := by
  have h := sum_projSquare D.adj
    (fun v v' => D.deg * (if v = v' then 1 else 0) + D.col v v') D.sign
    D.deg (-D.deg) D.mu D.card_ne_zero D.adj_symm D.sign_sq D.sign_sum
    (fun v => by simpa [deg] using D.adj_col_sum v)
    (fun v => by simpa [deg] using D.adj_sign v)
    (fun v v' => by simpa [deg] using D.adj_square v v') v v'
  simpa [colA] using h

/-- **The collinearity block, evaluated**, by `sum_projSquare` at
`(X, nu, xi, eta) = (col, q-1, q(q+1), q(q+1))`. -/
theorem sum_colC (v v' : V) :
    ∑ u, D.colC u v * D.colC u v'
      = (((D.ord ^ 2 - 1) * (if v = v' then 1 else 0) - 2 * D.col v v'
            + ((D.ord + 1) / 2) * (1 + D.sign v * D.sign v'))
          - 2 * (D.ord - 1) * D.col v v'
          + (D.ord - 1) ^ 2 * (if v = v' then 1 else 0)
          - (D.ord * D.deg - (D.ord - 1)) ^ 2 / ((Fintype.card V : ℕ) : ℚ)
          - ((D.ord * D.deg - (D.ord - 1)) ^ 2 / ((Fintype.card V : ℕ) : ℚ))
              * (D.sign v * D.sign v')) := by
  have h := sum_projSquare D.col
    (fun v v' => (D.ord ^ 2 - 1) * (if v = v' then 1 else 0) - 2 * D.col v v'
      + ((D.ord + 1) / 2) * (1 + D.sign v * D.sign v')) D.sign
    (D.ord * D.deg) (D.ord * D.deg) (D.ord - 1) D.card_ne_zero D.col_symm
    D.sign_sq D.sign_sum
    (fun v => by simpa [deg] using D.col_col_sum v)
    (fun v => by simpa [deg] using D.col_sign v)
    (fun v v' => D.col_square v v') v v'
  simpa [colC] using h

/-! ### The Gram factor -/

/-- The four rational square roots of the incidence coefficient. -/
noncomputable def factorA : Fin 4 → ℚ :=
  Classical.choose
    (TriangularHodgeLayer.exists_four_square_factor D.coeffA D.coeffA_nonneg)

theorem sum_sq_factorA : ∑ k, D.factorA k ^ 2 = D.coeffA :=
  Classical.choose_spec
    (TriangularHodgeLayer.exists_four_square_factor D.coeffA D.coeffA_nonneg)

/-- The four rational square roots of the collinearity coefficient. -/
noncomputable def factorC : Fin 4 → ℚ :=
  Classical.choose
    (TriangularHodgeLayer.exists_four_square_factor D.coeffC D.coeffC_nonneg)

theorem sum_sq_factorC : ∑ k, D.factorC k ^ 2 = D.coeffC :=
  Classical.choose_spec
    (TriangularHodgeLayer.exists_four_square_factor D.coeffC D.coeffC_nonneg)

/-- The four rational square roots of the rank-one weight. -/
noncomputable def factorW : Fin 4 → ℚ :=
  Classical.choose
    (TriangularHodgeLayer.exists_four_square_factor D.wCoeff D.wCoeff_nonneg)

theorem sum_sq_factorW : ∑ k, D.factorW k ^ 2 = D.wCoeff :=
  Classical.choose_spec
    (TriangularHodgeLayer.exists_four_square_factor D.wCoeff D.wCoeff_nonneg)

/-- The row index of the three-block Gram factor: the incidence square, the
collinearity square, and the rank-one remainder. -/
abbrev QuadRow (V : Type u) := (V × Fin 4) ⊕ ((V × Fin 4) ⊕ Fin 4)

/-- **The rational Gram factor**, in three blocks. -/
noncomputable def gramRow : QuadRow V → V → ℚ
  | Sum.inl p, v => D.factorA p.2 * D.colA p.1 v
  | Sum.inr (Sum.inl p), v => D.factorC p.2 * D.colC p.1 v
  | Sum.inr (Sum.inr k), v => D.factorW k * D.sign v

private theorem sum_block {W : Type u} [Fintype W] [DecidableEq W]
    (a : Fin 4 → ℚ) (B : W → V → ℚ) (v v' : V) :
    ∑ p : W × Fin 4, (a p.2 * B p.1 v) * (a p.2 * B p.1 v')
      = (∑ k, a k ^ 2) * (∑ u, B u v * B u v') := by
  classical
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The Gram matrix of `gramRow` splits into the two completed squares and the
rank-one remainder. -/
theorem sum_gramRow (v v' : V) :
    ∑ row : QuadRow V, D.gramRow row v * D.gramRow row v'
      = (∑ k, D.factorA k ^ 2) * (∑ u, D.colA u v * D.colA u v')
        + ((∑ k, D.factorC k ^ 2) * (∑ u, D.colC u v * D.colC u v')
          + (∑ k, D.factorW k ^ 2) * (D.sign v * D.sign v')) := by
  classical
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [← sum_block D.factorA D.colA v v']
    exact Finset.sum_congr rfl fun p _ => by simp only [gramRow]
  · rw [Fintype.sum_sum_type]
    congr 1
    · rw [← sum_block D.factorC D.colC v v']
      exact Finset.sum_congr rfl fun p _ => by simp only [gramRow]
    · rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by simp only [gramRow]; ring

/-- **The exact link identity for a generalized-quadrangle link.**

`L/d - gap * P0 - Qᵀ Q = 0` entrywise, with `gap = gapValue` and `Q = gramRow`.
The `col` coefficients of the two blocks cancel, `1/(2 mu d)` against
`-2q/(4 mu d q)`; the `delta` coefficients add to `1 - gap`; and the constant and
sign coefficients match once the vertex count is `2(q+1)(q²+1)`. -/
theorem gram_residual (v v' : V) :
    ((if v = v' then D.deg else 0) - D.adj v v') / D.deg
        - D.gapValue * ((if v = v' then (1 : ℚ) else 0)
            - 1 / ((Fintype.card V : ℕ) : ℚ))
        - ∑ row : QuadRow V, D.gramRow row v * D.gramRow row v' = 0 := by
  classical
  have hd : D.deg ≠ 0 := D.deg_ne_zero
  have hq : D.ord ≠ 0 := D.ord_ne_zero
  have hm : D.mu ≠ 0 := D.mu_ne_zero
  have hn : (2 : ℚ) * (D.ord + 1) * (D.ord ^ 2 + 1) ≠ 0 := by
    have h := D.ord_pos
    have hpos : (0 : ℚ) < 2 * (D.ord + 1) * (D.ord ^ 2 + 1) := by
      nlinarith [sq_nonneg D.ord]
    exact ne_of_gt hpos
  have hK : (if v = v' then D.deg else 0)
      = D.deg * (if v = v' then (1 : ℚ) else 0) := by
    split_ifs <;> ring
  rw [hK, D.sum_gramRow v v', D.sum_sq_factorA, D.sum_sq_factorC,
    D.sum_sq_factorW, D.sum_colA v v', D.sum_colC v v']
  simp only [gapValue, contraction, wCoeff, coeffA, coeffC, deg, D.card_eq]
  field_simp
  ring

/-! ### The certificate -/

/-- **A generalized-quadrangle link discharges the `k`-gonal certificate at
`k = 3`.**  Everything but the regularity of the presentation link and the
identification of its adjacency counts is proved. -/
theorem linkCertificateChecks_kgon_of_quadrangle
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Nonempty Generator] [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Q : QuadrangleLinkData (Generator × Bool)) (d : ℕ)
    (hdegval : (d : ℚ) = Q.deg)
    (hadj : ∀ u v, (TriangularHodgeLayer.adjacencyCount T u v : ℚ) = Q.adj u v) :
    LinkCertificateChecks_kgon 3
      (fun u v => (TriangularHodgeLayer.adjacencyCount T u v : ℚ))
      (d : ℚ) Q.gapValue (1 / 2) Q.gramRow := by
  classical
  refine ⟨le_rfl, ?_, Q.gapValue_gt_half, ?_, ?_⟩
  · rw [hdegval]
    exact Q.deg_pos
  · intro v
    rw [show (∑ u, ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ))
        = ∑ u, Q.adj u v from Finset.sum_congr rfl fun u _ => hadj u v]
    rw [hdegval]
    exact Q.adj_col_sum v
  · intro v v'
    have hres := Q.gram_residual v v'
    rw [hadj v v', hdegval]
    exact hres

/-- **A triangular presentation whose link is the incidence graph of a
generalized quadrangle of order `q ≥ 7` has property `(T)`.**

Every analytic and spectral step is discharged: the two completed squares give
the rational Gram factor, `LinkCertificateChecks_kgon` at `k = 3` is the
repository's link certificate, and the Garland certificate of
`Kazhdan/TriangularHodgeLayer.lean` turns it into a Kazhdan pair.  What the
caller supplies is a finite table. -/
theorem hasKazhdanPropertyT_of_quadrangleLink
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Nonempty Generator] [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Q : QuadrangleLinkData (Generator × Bool)) (d : ℕ)
    (hdeg : ∀ u, TriangularHodgeLayer.degree T u = d)
    (hdegval : (d : ℚ) = Q.deg)
    (hadj : ∀ u v, (TriangularHodgeLayer.adjacencyCount T u v : ℚ) = Q.adj u v) :
    HasKazhdanPropertyT.{0, 0} (TriangularHodgeLayer.Presented T) :=
  hasKazhdanPropertyT_of_kgonChecks_three T d Q.gapValue Q.gramRow hdeg
    (linkCertificateChecks_kgon_of_quadrangle T Q d hdegval hadj)

end QuadrangleLinkData

/-! ## The arithmetic at `q = 8` -/

/-- At `q = 8` the threshold interval for `mu` is nonempty and contains the
integer `4`: `16 - 36 + 16 = -4 < 0`. -/
theorem quadrangleMuBound_eight : (4 : ℚ) ^ 2 - 4 * (8 + 1) + 2 * 8 < 0 := by
  norm_num

/-- At `q = 8` and `mu = 4` the contraction constant is `4/9`, so the gap is
`5/9`. -/
theorem quadrangleContraction_eight :
    (2 * 8 + (4 : ℚ) ^ 2) / (2 * 4 * (8 + 1)) = 4 / 9 := by
  norm_num

/-- The threshold `mu² - mu(q+1) + 2q < 0` is solvable exactly when
`(q+1)² > 8q`; at `q = 7` the discriminant is `17 > 0`, and at `q = 5` it is
`-4 < 0`, which is why the smallest admissible order is `7`. -/
theorem quadrangleDiscriminant_seven : (0 : ℚ) < (7 + 1) ^ 2 - 8 * 7 := by
  norm_num

theorem quadrangleDiscriminant_five : ((5 : ℚ) + 1) ^ 2 - 8 * 5 < 0 := by
  norm_num

/-- **Generalized hexagons are worse, not better.**  The incidence graph of a
generalized hexagon of order `(q,q)` is `(q+1)`-regular of girth `12` with
largest non-principal eigenvalue `√(3q)`, so the threshold is
`4 * 3q < (q+1)²`, that is `q² - 10q + 1 > 0`, needing `q ≥ 11`; and the point
count `(1+q)(1+q²+q⁴)` is then `177156`, against `585` for the quadrangle at
`q = 8`.  The hexagon's threshold rises while its point count grows like `q⁵`. -/
theorem hexagonThreshold_eleven : (0 : ℚ) < 11 ^ 2 - 10 * 11 + 1 := by
  norm_num

theorem hexagonThreshold_nine : ((9 : ℚ) ^ 2 - 10 * 9 + 1) < 0 := by
  norm_num

theorem hexagonPointCount_eleven : (1 + 11) * (1 + 11 ^ 2 + 11 ^ 4) = 177156 := by
  norm_num

end KazhdanHyp
end GroupApproximation
