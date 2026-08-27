import GroupApproximation.Kazhdan.TriangularHodgeLayer

/-!
# Rational link certificates from bipartite spectral data

`Kazhdan/TriangularHodgeLayer.lean` ends at
`presented_hasKazhdanPropertyT_of_linkCertificate`: a triangular presentation
whose presentation-link table is `d`-regular and admits an exact rational
identity

```
    L / d = gap * P0 + Qᵀ Q ,        gap > 1/2
```

has property `(T)`.  That is Zuk's criterion, and it is already proved in this
repository.  What it consumes is the finite rational Gram factor `Q`, and
nothing in the repository produces one.

This module produces one, for the only links that can carry it: the incidence
graph of a finite projective plane.

## The algebra

`BipartiteLinkData` is a finite vertex set `V` carrying

* a symmetric rational adjacency table `adj` with all column sums `deg`;
* a bipartition sign `sign : V → ℚ` with `sign u * sign u = 1`, `∑ sign = 0`,
  and `∑ u, adj u v * sign u = -(deg * sign v)` --- the statement that `sign` is
  a `(-deg)`-eigenvector, i.e. that the graph is bipartite;
* the **two-step identity**
  `∑ u, adj u v * adj u v' = ev * δ(v,v') + (1 + sign v * sign v') / 2`,
  which says: two vertices on the same side have exactly one common neighbour
  unless they are equal, in which case they have `ev + 1`; two vertices on
  opposite sides have none.

The incidence graph of a projective plane of order `q` satisfies this with
`ev = q` and `deg = q + 1`, because `N Nᵀ = q I + J` for the incidence matrix.
No other input is used, and no eigenvalue is ever named: the whole certificate
is a completed square.

Write `n = card V`, `μ = deg / 2`, and

```
    B u v = adj u v - μ δ(u,v) - deg/(2n) + 3 deg/(2n) * sign u * sign v .
```

`B` is `A - μ` projected off the two-dimensional span of the constant vector
and of `sign`; the two correction coefficients are exactly `(deg-μ)/n` and
`(deg+μ)/n`, which is what makes `B` kill both.  Expanding `∑ u, B u v * B u v'`
with the five hypotheses above gives (`sum_colB_mul_colB`)

```
    ∑ u, B u v * B u v' = (ev + μ²) δ(v,v') - 2μ adj v v'
        + (1/2 - (deg-μ)²/n) + (1/2 - (deg+μ)²/n) sign v sign v' ,
```

and dividing by `deg²` matches `L/deg - gap * P0` in the `δ` and `adj`
coefficients on the nose once

```
    gap = 3/4 - ev / deg² .
```

The remaining constant and `sign`-coefficients match precisely when
`n = 2 (deg² - ev)`, which for a projective plane is the count
`q² + q + 1 = (q+1)² - q` of points --- and that count is *derived* here
(`ProjectivePlaneData.card_eq`) rather than assumed.  The leftover
`sign ⊗ sign` weight is `(2 - gap)/n > 0`, and Lagrange's four-square theorem
turns it into four rational rows (`wFactor`).  So the Gram factor is

```
    Row = V ⊕ Fin 4 ,   Q (inl u) v = B u v / deg ,   Q (inr k) v = a k * sign v .
```

## Why the threshold is met

`gap > 1/2` reads `4 ev < deg²`, and for a projective plane of order `q` that
is `4q < (q+1)²`, i.e. `(q - 1)² > 0`: **every** projective plane of order
`q ≥ 2` clears Zuk's threshold, with room to spare.  The classical form of this
computation names the eigenvalue `1 - √q/(q+1)` of the normalized Laplacian of
the incidence graph; the completed square above avoids the square root entirely,
which is what lets the certificate stay inside `ℚ`.

## What this module does not do

It does not exhibit a triangular presentation whose link is such a graph.  That
is the input `hadj` of `hasKazhdanPropertyT_of_linkData`, and
`GGT/KazhdanHyp.lean` records what is known about supplying it, and what the
resulting group can and cannot be.
-/

namespace GroupApproximation
namespace KazhdanHyp

universe u

/-! ## Finite sum helpers

Each of these is the evaluation of one Kronecker-delta sum; they are the only
place where the finiteness of the vertex set is used. -/

private theorem sum_kron_mul {α : Type u} [Fintype α] [DecidableEq α]
    (f : α → ℚ) (v : α) :
    ∑ u, (if u = v then (1 : ℚ) else 0) * f u = f v := by
  classical
  simp

private theorem sum_mul_kron {α : Type u} [Fintype α] [DecidableEq α]
    (f : α → ℚ) (v : α) :
    ∑ u, f u * (if u = v then (1 : ℚ) else 0) = f v := by
  classical
  simp

private theorem sum_kron_kron {α : Type u} [Fintype α] [DecidableEq α] (v v' : α) :
    ∑ u : α, (if u = v then (1 : ℚ) else 0) * (if u = v' then (1 : ℚ) else 0)
      = if v = v' then 1 else 0 :=
  sum_kron_mul (fun u => if u = v' then (1 : ℚ) else 0) v

private theorem sum_kron {α : Type u} [Fintype α] [DecidableEq α] (v : α) :
    ∑ u : α, (if u = v then (1 : ℚ) else 0) = 1 := by
  classical
  simp

private theorem sum_kron_left {α : Type u} [Fintype α] [DecidableEq α] (v : α) :
    ∑ u : α, (if v = u then (1 : ℚ) else 0) = 1 := by
  classical
  simp

private theorem sum_one {α : Type u} [Fintype α] :
    ∑ _u : α, (1 : ℚ) = (Fintype.card α : ℚ) := by
  simp

/-! ## Bipartite link data -/

/-- **A bipartite link table with a two-step identity.**  The five combinatorial
hypotheses are exactly what the incidence graph of a finite projective plane
supplies; `card_eq` is the vertex count forced by them, and `ev_lt` is Zuk's
threshold in the form that carries no square root. -/
structure BipartiteLinkData (V : Type u) [Fintype V] [DecidableEq V] where
  /-- The rational adjacency table of the link. -/
  adj : V → V → ℚ
  /-- The bipartition sign, valued in `±1`. -/
  sign : V → ℚ
  /-- The common vertex degree. -/
  deg : ℚ
  /-- The two-step constant: `q` for the incidence graph of a plane of order
  `q`. -/
  ev : ℚ
  /-- The table is symmetric. -/
  adj_symm : ∀ u v, adj u v = adj v u
  /-- The sign is valued in `±1`. -/
  sign_sq : ∀ u, sign u * sign u = 1
  /-- The two sides have equal size. -/
  sign_sum : ∑ u, sign u = 0
  /-- Every column sums to the degree. -/
  col_sum : ∀ v, ∑ u, adj u v = deg
  /-- The sign is a `(-deg)`-eigenvector: the graph is bipartite. -/
  sign_col : ∀ v, ∑ u, adj u v * sign u = -(deg * sign v)
  /-- **The two-step identity.**  Same-side vertices have one common neighbour,
  or `ev + 1` if equal; opposite-side vertices have none. -/
  square : ∀ v v', ∑ u, adj u v * adj u v'
      = ev * (if v = v' then 1 else 0) + (1 + sign v * sign v') / 2
  /-- The vertex count forced by the identities. -/
  card_eq : (Fintype.card V : ℚ) = 2 * (deg ^ 2 - ev)
  /-- The degree is positive. -/
  deg_pos : 0 < deg
  /-- The two-step constant is nonnegative. -/
  ev_nonneg : 0 ≤ ev
  /-- **Zuk's threshold**, square-root free. -/
  ev_lt : 4 * ev < deg ^ 2

namespace BipartiteLinkData

variable {V : Type u} [Fintype V] [DecidableEq V] (D : BipartiteLinkData V)

/-- The degree is nonzero. -/
theorem deg_ne_zero : D.deg ≠ 0 := ne_of_gt D.deg_pos

/-- The vertex count is positive, in the form used to clear denominators. -/
theorem sq_sub_pos : 0 < D.deg ^ 2 - D.ev := by
  have h1 := D.ev_nonneg
  have h2 := D.ev_lt
  linarith

/-- **The link gap.**  For the incidence graph of a plane of order `q` this is
`3/4 - q/(q+1)²`, a rational number below the true first nonzero eigenvalue
`1 - √q/(q+1)` of the normalized Laplacian and above `1/2`. -/
def gapValue : ℚ := 3 / 4 - D.ev / D.deg ^ 2

/-- **The gap clears Zuk's threshold.**  This is `4 ev < deg²` restated. -/
theorem gapValue_gt_half : (1 : ℚ) / 2 < D.gapValue := by
  have hd : (0 : ℚ) < D.deg ^ 2 := pow_pos D.deg_pos 2
  have h : D.ev / D.deg ^ 2 < 1 / 4 := by
    rw [div_lt_iff₀ hd]
    have := D.ev_lt
    linarith
  unfold gapValue
  linarith

/-- The gap never exceeds `3/4`. -/
theorem gapValue_le : D.gapValue ≤ 3 / 4 := by
  have h : 0 ≤ D.ev / D.deg ^ 2 :=
    div_nonneg D.ev_nonneg (le_of_lt (pow_pos D.deg_pos 2))
  unfold gapValue
  linarith

/-- The rank-one weight the bipartition eigenvector still carries after the
completed square has been removed. -/
def wCoeff : ℚ := (2 - D.gapValue) / (Fintype.card V : ℚ)

/-- The weight is nonnegative, so Lagrange's theorem applies to it. -/
theorem wCoeff_nonneg : 0 ≤ D.wCoeff := by
  have hcard : (0 : ℚ) < (Fintype.card V : ℚ) := by
    rw [D.card_eq]
    have := D.sq_sub_pos
    linarith
  have hg := D.gapValue_le
  exact div_nonneg (by linarith) (le_of_lt hcard)

/-- The four rational square roots of `wCoeff`, from Lagrange's four-square
theorem in the rational form proved in `Kazhdan/TriangularHodgeLayer.lean`. -/
noncomputable def wFactor : Fin 4 → ℚ :=
  Classical.choose
    (TriangularHodgeLayer.exists_four_square_factor D.wCoeff D.wCoeff_nonneg)

theorem sum_sq_wFactor : ∑ k, D.wFactor k ^ 2 = D.wCoeff :=
  Classical.choose_spec
    (TriangularHodgeLayer.exists_four_square_factor D.wCoeff D.wCoeff_nonneg)

/-! ### The completed square -/

/-- Half the degree: the shift that completes the square. -/
def cMid : ℚ := D.deg / 2

/-- The constant-vector correction `(deg - cMid)/n`. -/
def cJ : ℚ := D.deg / (2 * (Fintype.card V : ℚ))

/-- The sign-vector correction `(deg + cMid)/n`. -/
def cW : ℚ := 3 * D.deg / (2 * (Fintype.card V : ℚ))

/-- **The Gram column.**  `adj - cMid` corrected so as to annihilate both the
constant vector and the bipartition sign. -/
def colB (u v : V) : ℚ :=
  D.adj u v - D.cMid * (if u = v then 1 else 0) - D.cJ + D.cW * (D.sign u * D.sign v)

/-- **The completed square, evaluated.**  Every one of the sixteen terms of the
expansion is one of the five structural sums, and the result is a linear
combination of `δ(v,v')`, `adj v v'`, `1` and `sign v * sign v'`. -/
theorem sum_colB_mul_colB (v v' : V) :
    ∑ u, D.colB u v * D.colB u v'
      = (D.ev + D.cMid ^ 2) * (if v = v' then 1 else 0)
        - 2 * D.cMid * D.adj v v'
        + (1 / 2 - 2 * D.cJ * D.deg + 2 * D.cJ * D.cMid
            + D.cJ ^ 2 * (Fintype.card V : ℚ))
        + (1 / 2 - 2 * D.cW * D.deg - 2 * D.cMid * D.cW
            + D.cW ^ 2 * (Fintype.card V : ℚ)) * (D.sign v * D.sign v') := by
  classical
  have e1 : ∑ u, D.adj u v * D.adj u v'
      = D.ev * (if v = v' then 1 else 0) + (1 + D.sign v * D.sign v') / 2 :=
    D.square v v'
  have e2 : ∑ u, (if u = v then (1 : ℚ) else 0) * D.adj u v' = D.adj v v' :=
    sum_kron_mul (fun u => D.adj u v') v
  have e3 : ∑ u, D.adj u v * (if u = v' then (1 : ℚ) else 0) = D.adj v v' := by
    have h : ∑ u, D.adj u v * (if u = v' then (1 : ℚ) else 0) = D.adj v' v :=
      sum_mul_kron (fun u => D.adj u v) v'
    rw [h]
    exact D.adj_symm v' v
  have e4 : ∑ u : V, (if u = v then (1 : ℚ) else 0) * (if u = v' then (1 : ℚ) else 0)
      = if v = v' then 1 else 0 := sum_kron_kron v v'
  have e5 : ∑ u, D.adj u v' = D.deg := D.col_sum v'
  have e6 : ∑ u, D.adj u v = D.deg := D.col_sum v
  have e7 : ∑ u : V, (if u = v then (1 : ℚ) else 0) = 1 := sum_kron v
  have e8 : ∑ u : V, (if u = v' then (1 : ℚ) else 0) = 1 := sum_kron v'
  have e9 : ∑ _u : V, (1 : ℚ) = (Fintype.card V : ℚ) := sum_one
  have e10 : ∑ u, D.adj u v * D.sign u = -(D.deg * D.sign v) := D.sign_col v
  have e11 : ∑ u, D.adj u v' * D.sign u = -(D.deg * D.sign v') := D.sign_col v'
  have e12 : ∑ u, (if u = v then (1 : ℚ) else 0) * D.sign u = D.sign v :=
    sum_kron_mul D.sign v
  have e13 : ∑ u, (if u = v' then (1 : ℚ) else 0) * D.sign u = D.sign v' :=
    sum_kron_mul D.sign v'
  have e14 : ∑ u, D.sign u = 0 := D.sign_sum
  have e15 : ∑ u : V, D.sign u * D.sign u = (Fintype.card V : ℚ) := by
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset V) = Finset.univ) fun u _ => D.sign_sq u]
    exact sum_one
  have key : ∑ u, D.colB u v * D.colB u v'
      = (∑ u, D.adj u v * D.adj u v')
        - D.cMid * (∑ u, (if u = v then (1 : ℚ) else 0) * D.adj u v')
        - D.cMid * (∑ u, D.adj u v * (if u = v' then (1 : ℚ) else 0))
        + D.cMid ^ 2 *
            (∑ u : V, (if u = v then (1 : ℚ) else 0) * (if u = v' then (1 : ℚ) else 0))
        - D.cJ * (∑ u, D.adj u v')
        - D.cJ * (∑ u, D.adj u v)
        + D.cJ * D.cMid * (∑ u : V, (if u = v then (1 : ℚ) else 0))
        + D.cJ * D.cMid * (∑ u : V, (if u = v' then (1 : ℚ) else 0))
        + D.cJ ^ 2 * (∑ _u : V, (1 : ℚ))
        + D.cW * D.sign v' * (∑ u, D.adj u v * D.sign u)
        + D.cW * D.sign v * (∑ u, D.adj u v' * D.sign u)
        - D.cW * D.cMid * D.sign v' * (∑ u, (if u = v then (1 : ℚ) else 0) * D.sign u)
        - D.cW * D.cMid * D.sign v * (∑ u, (if u = v' then (1 : ℚ) else 0) * D.sign u)
        - D.cJ * D.cW * D.sign v * (∑ u, D.sign u)
        - D.cJ * D.cW * D.sign v' * (∑ u, D.sign u)
        + D.cW ^ 2 * D.sign v * D.sign v' * (∑ u : V, D.sign u * D.sign u) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by simp only [colB]; ring
  rw [key, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  ring

/-! ### The Gram factor -/

/-- **The rational Gram factor.**  The completed square, scaled by `1/deg`, on
the left; the four Lagrange rows of the leftover rank-one weight on the
right. -/
noncomputable def gramRow : (V ⊕ Fin 4) → V → ℚ
  | Sum.inl u, v => 1 / D.deg * D.colB u v
  | Sum.inr k, v => D.wFactor k * D.sign v

/-- The Gram matrix of `gramRow` splits into the completed square and the
rank-one remainder. -/
theorem sum_gramRow (v v' : V) :
    ∑ row : V ⊕ Fin 4, D.gramRow row v * D.gramRow row v'
      = (1 / D.deg) ^ 2 * (∑ u, D.colB u v * D.colB u v')
        + (∑ k, D.wFactor k ^ 2) * (D.sign v * D.sign v') := by
  classical
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by simp only [gramRow]; ring
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by simp only [gramRow]; ring

/-- **The exact link identity.**  `L/deg - gap * P0 - Qᵀ Q = 0` entrywise, with
`gap = gapValue` and `Q = gramRow`.  This is the residual that
`TriangularHodgeLayer.LinkCertificateChecks` asks to vanish, stated for abstract
link data. -/
theorem gram_residual (v v' : V) :
    ((if v = v' then D.deg else 0) - D.adj v v') / D.deg
        - D.gapValue * ((if v = v' then (1 : ℚ) else 0) - 1 / (Fintype.card V : ℚ))
        - ∑ row : V ⊕ Fin 4, D.gramRow row v * D.gramRow row v' = 0 := by
  classical
  have hd : D.deg ≠ 0 := D.deg_ne_zero
  have hszpos : (0 : ℚ) < 2 * (D.deg ^ 2 - D.ev) := by
    have := D.sq_sub_pos
    linarith
  have hsz : (2 : ℚ) * (D.deg ^ 2 - D.ev) ≠ 0 := ne_of_gt hszpos
  have hK : (if v = v' then D.deg else 0) = D.deg * (if v = v' then (1 : ℚ) else 0) := by
    split_ifs <;> ring
  rw [hK, D.sum_gramRow v v', D.sum_colB_mul_colB v v', D.sum_sq_wFactor]
  simp only [gapValue, wCoeff, cMid, cJ, cW, D.card_eq]
  field_simp
  ring

end BipartiteLinkData

/-! ## Projective planes

The only input the certificate needs is a table with `N Nᵀ = q I + J` and
`Nᵀ N = q I + J`.  That is a finite projective plane of order `q`, written
without any incidence geometry: `inc x y` is the rational `0/1` entry saying
that point `x` lies on line `y`. -/

/-- **A finite projective plane of order `order`, as a rational incidence
table.**  Points and lines are both indexed by `P`; `rowPair` and `colPair` are
`N Nᵀ = order · I + J` and `Nᵀ N = order · I + J`, the statements that two
distinct points lie on exactly one common line and two distinct lines meet in
exactly one point. -/
structure ProjectivePlaneData (P : Type u) [Fintype P] [DecidableEq P] where
  /-- The incidence table. -/
  inc : P → P → ℚ
  /-- The order of the plane. -/
  order : ℚ
  /-- Only orders above one clear Zuk's threshold, and order one is the
  degenerate plane. -/
  order_gt_one : 1 < order
  /-- Every point lies on `order + 1` lines. -/
  rowSum : ∀ x, ∑ y, inc x y = order + 1
  /-- Every line carries `order + 1` points. -/
  colSum : ∀ y, ∑ x, inc x y = order + 1
  /-- Two distinct points lie on exactly one common line. -/
  rowPair : ∀ x x', ∑ y, inc x y * inc x' y = order * (if x = x' then 1 else 0) + 1
  /-- Two distinct lines meet in exactly one point. -/
  colPair : ∀ y y', ∑ x, inc x y * inc x y' = order * (if y = y' then 1 else 0) + 1

namespace ProjectivePlaneData

variable {P : Type u} [Fintype P] [DecidableEq P] (Pl : ProjectivePlaneData P)

/-- **The point count is forced.**  Summing `rowPair x x'` over `x'` two ways
gives `order + card P = (order + 1)²`, the classical `q² + q + 1`.  Nothing
assumes it. -/
theorem card_eq [Nonempty P] : (Fintype.card P : ℚ) = (Pl.order + 1) ^ 2 - Pl.order := by
  classical
  obtain ⟨x⟩ := ‹Nonempty P›
  have h1 : ∑ x' : P, (∑ y, Pl.inc x y * Pl.inc x' y)
      = Pl.order + (Fintype.card P : ℚ) := by
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset P) = Finset.univ)
        (fun x' _ => Pl.rowPair x x'),
      Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_kron_left x, sum_one]
    ring
  have h2 : ∑ x' : P, (∑ y, Pl.inc x y * Pl.inc x' y) = (Pl.order + 1) ^ 2 := by
    rw [Finset.sum_comm]
    have hy : ∀ y : P, ∑ x' : P, Pl.inc x y * Pl.inc x' y
        = Pl.inc x y * (Pl.order + 1) := by
      intro y
      rw [← Finset.mul_sum, Pl.colSum y]
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset P) = Finset.univ)
        (fun y _ => hy y),
      ← Finset.sum_mul, Pl.rowSum x]
    ring
  linarith [h1, h2]

/-! ### The incidence graph -/

/-- **The incidence graph of the plane**, on `P × Bool`: the `true` copy of `P`
is the points, the `false` copy is the lines, and the two are joined by
`inc`. -/
def linkAdj : P × Bool → P × Bool → ℚ := fun u v =>
  if u.2 then (if v.2 then 0 else Pl.inc u.1 v.1)
  else (if v.2 then Pl.inc v.1 u.1 else 0)

/-- The bipartition sign of the incidence graph. -/
def linkSign : P × Bool → ℚ := fun u => if u.2 then 1 else -1

theorem linkAdj_tt (x y : P) : Pl.linkAdj (x, true) (y, true) = 0 := rfl

theorem linkAdj_tf (x y : P) : Pl.linkAdj (x, true) (y, false) = Pl.inc x y := rfl

theorem linkAdj_ft (x y : P) : Pl.linkAdj (x, false) (y, true) = Pl.inc y x := rfl

theorem linkAdj_ff (x y : P) : Pl.linkAdj (x, false) (y, false) = 0 := rfl

theorem linkSign_t (x : P) : Pl.linkSign (x, true) = 1 := rfl

theorem linkSign_f (x : P) : Pl.linkSign (x, false) = -1 := rfl

/-- The incidence graph is symmetric. -/
theorem linkAdj_symm (u v : P × Bool) : Pl.linkAdj u v = Pl.linkAdj v u := by
  obtain ⟨x, s⟩ := u
  obtain ⟨y, t⟩ := v
  cases s <;> cases t <;>
    simp only [linkAdj_tt, linkAdj_tf, linkAdj_ft, linkAdj_ff]

/-- Every column of the incidence graph sums to `order + 1`. -/
theorem linkAdj_col_sum (v : P × Bool) :
    ∑ u : P × Bool, Pl.linkAdj u v = Pl.order + 1 := by
  classical
  obtain ⟨y, t⟩ := v
  rw [Fintype.sum_prod_type]
  cases t
  · have h : ∀ x : P, ∑ s : Bool, Pl.linkAdj (x, s) (y, false) = Pl.inc x y := by
      intro x
      simp only [Fintype.sum_bool, linkAdj_tf, linkAdj_ff]
      ring
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset P) = Finset.univ) fun x _ => h x]
    exact Pl.colSum y
  · have h : ∀ x : P, ∑ s : Bool, Pl.linkAdj (x, s) (y, true) = Pl.inc y x := by
      intro x
      simp only [Fintype.sum_bool, linkAdj_tt, linkAdj_ft]
      ring
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset P) = Finset.univ) fun x _ => h x]
    exact Pl.rowSum y

/-- The sign is a `-(order + 1)`-eigenvector: the incidence graph is
bipartite. -/
theorem linkAdj_sign_col (v : P × Bool) :
    ∑ u : P × Bool, Pl.linkAdj u v * Pl.linkSign u
      = -((Pl.order + 1) * Pl.linkSign v) := by
  classical
  obtain ⟨y, t⟩ := v
  rw [Fintype.sum_prod_type]
  cases t
  · have h : ∀ x : P, ∑ s : Bool, Pl.linkAdj (x, s) (y, false) * Pl.linkSign (x, s)
        = Pl.inc x y := by
      intro x
      simp only [Fintype.sum_bool, linkAdj_tf, linkAdj_ff, linkSign_t, linkSign_f]
      ring
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset P) = Finset.univ)
        (fun x _ => h x),
      Pl.colSum y, linkSign_f]
    ring
  · have h : ∀ x : P, ∑ s : Bool, Pl.linkAdj (x, s) (y, true) * Pl.linkSign (x, s)
        = -1 * Pl.inc y x := by
      intro x
      simp only [Fintype.sum_bool, linkAdj_tt, linkAdj_ft, linkSign_t, linkSign_f]
      ring
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset P) = Finset.univ)
        (fun x _ => h x),
      ← Finset.mul_sum, Pl.rowSum y,
      linkSign_t]
    ring

/-- **The two-step identity for the incidence graph.**  Same-side vertices have
one common neighbour unless equal, when they have `order + 1`; opposite-side
vertices have none.  This is `N Nᵀ = order · I + J` together with its
transpose. -/
theorem linkAdj_square (v v' : P × Bool) :
    ∑ u : P × Bool, Pl.linkAdj u v * Pl.linkAdj u v'
      = Pl.order * (if v = v' then 1 else 0)
        + (1 + Pl.linkSign v * Pl.linkSign v') / 2 := by
  classical
  obtain ⟨y, t⟩ := v
  obtain ⟨y', t'⟩ := v'
  rw [Fintype.sum_prod_type]
  cases t <;> cases t'
  · have h : ∀ x : P,
        ∑ s : Bool, Pl.linkAdj (x, s) (y, false) * Pl.linkAdj (x, s) (y', false)
          = Pl.inc x y * Pl.inc x y' := by
      intro x
      simp only [Fintype.sum_bool, linkAdj_tf, linkAdj_ff]
      ring
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset P) = Finset.univ)
        (fun x _ => h x),
      Pl.colPair y y']
    by_cases hy : y = y'
    · subst hy
      norm_num [linkSign_f]
    · norm_num [linkSign_f, Prod.mk.injEq, hy]
  · have h : ∀ x : P,
        ∑ s : Bool, Pl.linkAdj (x, s) (y, false) * Pl.linkAdj (x, s) (y', true)
          = 0 := by
      intro x
      simp only [Fintype.sum_bool, linkAdj_tf, linkAdj_tt, linkAdj_ff, linkAdj_ft]
      ring
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset P) = Finset.univ) fun x _ => h x]
    norm_num [linkSign_t, linkSign_f, Prod.mk.injEq]
  · have h : ∀ x : P,
        ∑ s : Bool, Pl.linkAdj (x, s) (y, true) * Pl.linkAdj (x, s) (y', false)
          = 0 := by
      intro x
      simp only [Fintype.sum_bool, linkAdj_tf, linkAdj_tt, linkAdj_ff, linkAdj_ft]
      ring
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset P) = Finset.univ) fun x _ => h x]
    norm_num [linkSign_t, linkSign_f, Prod.mk.injEq]
  · have h : ∀ x : P,
        ∑ s : Bool, Pl.linkAdj (x, s) (y, true) * Pl.linkAdj (x, s) (y', true)
          = Pl.inc y x * Pl.inc y' x := by
      intro x
      simp only [Fintype.sum_bool, linkAdj_tt, linkAdj_ft]
      ring
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset P) = Finset.univ)
        (fun x _ => h x),
      Pl.rowPair y y']
    by_cases hy : y = y'
    · subst hy
      norm_num [linkSign_t]
    · norm_num [linkSign_t, Prod.mk.injEq, hy]

/-- **The incidence graph of a projective plane is bipartite link data.**  Every
field is one of the identities above; `card_eq` is the derived point count, and
`ev_lt` is `4q < (q+1)²`, which holds for every order above one. -/
def linkData [Nonempty P] : BipartiteLinkData (P × Bool) where
  adj := Pl.linkAdj
  sign := Pl.linkSign
  deg := Pl.order + 1
  ev := Pl.order
  adj_symm := Pl.linkAdj_symm
  sign_sq := by
    intro u
    obtain ⟨x, s⟩ := u
    cases s <;> norm_num [linkSign_t, linkSign_f]
  sign_sum := by
    classical
    rw [Fintype.sum_prod_type]
    have h : ∀ x : P, ∑ s : Bool, Pl.linkSign (x, s) = 0 := by
      intro x
      simp only [Fintype.sum_bool, linkSign_t, linkSign_f]
      ring
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset P) = Finset.univ) fun x _ => h x]
    simp
  col_sum := Pl.linkAdj_col_sum
  sign_col := Pl.linkAdj_sign_col
  square := Pl.linkAdj_square
  card_eq := by
    have hcard : (Fintype.card (P × Bool) : ℚ) = (Fintype.card P : ℚ) * 2 := by
      rw [Fintype.card_prod, Fintype.card_bool]
      push_cast
      ring
    rw [hcard, Pl.card_eq]
    ring
  deg_pos := by linarith [Pl.order_gt_one]
  ev_nonneg := by linarith [Pl.order_gt_one]
  ev_lt := by
    have h : (0 : ℚ) < (Pl.order - 1) * (Pl.order - 1) :=
      mul_pos (by linarith [Pl.order_gt_one]) (by linarith [Pl.order_gt_one])
    nlinarith [h]

theorem linkData_deg [Nonempty P] : (Pl.linkData).deg = Pl.order + 1 := rfl

theorem linkData_ev [Nonempty P] : (Pl.linkData).ev = Pl.order := rfl

theorem linkData_adj [Nonempty P] (u v : P × Bool) : (Pl.linkData).adj u v = Pl.linkAdj u v := rfl

/-- **The gap of a projective-plane link, in closed form.**  For order `q` it is
`3/4 - q/(q+1)²`, and `BipartiteLinkData.gapValue_gt_half` says it exceeds
`1/2`. -/
theorem linkData_gapValue [Nonempty P] :
    (Pl.linkData).gapValue = 3 / 4 - Pl.order / (Pl.order + 1) ^ 2 := rfl

end ProjectivePlaneData

/-! ## The bridge to the repository's Garland certificate

`TriangularHodgeLayer.LinkCertificateChecks` is a predicate on a triangular
presentation `T`, a natural regular degree, a rational gap and a rational Gram
factor.  Its three combinatorial clauses are the positivity of the degree, the
half-threshold, and the regularity of the presentation link; its fourth is
exactly `BipartiteLinkData.gram_residual`. -/

/-- **Abstract link data discharges the repository's link certificate.**  The
only inputs are that the presentation link of `T` is `d`-regular and that its
adjacency counts are the entries of `D`. -/
theorem linkCertificateChecks_of_linkData
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Nonempty Generator] [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (D : BipartiteLinkData (Generator × Bool)) (d : ℕ)
    (hdeg : ∀ u, TriangularHodgeLayer.degree T u = d)
    (hdegval : (d : ℚ) = D.deg)
    (hadj : ∀ u v, (TriangularHodgeLayer.adjacencyCount T u v : ℚ) = D.adj u v) :
    TriangularHodgeLayer.LinkCertificateChecks T d D.gapValue D.gramRow := by
  classical
  have hdpos : 0 < d := by
    have h : (0 : ℚ) < (d : ℚ) := by
      rw [hdegval]
      exact D.deg_pos
    exact_mod_cast h
  have hlap : ∀ u v, TriangularHodgeLayer.rationalLinkLaplacian T u v
      = (if u = v then D.deg else 0) - D.adj u v := by
    intro u v
    have h1 : TriangularHodgeLayer.rationalLinkLaplacian T u v
        = (if u = v then ((TriangularHodgeLayer.degree T u : ℕ) : ℚ) else 0)
          - ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ) := by
      simp only [TriangularHodgeLayer.rationalLinkLaplacian,
        TriangularHodgeLayer.linkLaplacian]
      push_cast [apply_ite (fun z : ℤ => (z : ℚ))]
    rw [h1, hdeg u, hadj u v, hdegval]
  refine ⟨hdpos, D.gapValue_gt_half, hdeg, ?_⟩
  intro u v
  have hres := D.gram_residual u v
  simp only [TriangularHodgeLayer.linkGapResidual, TriangularHodgeLayer.meanZeroProjector,
    TriangularHodgeLayer.gramMatrix, hlap u v, hdegval]
  exact hres

/-- **A triangular presentation whose link carries bipartite spectral data has
property `(T)`.**  This is Zuk's criterion, assembled from
`TriangularHodgeLayer.presented_hasKazhdanPropertyT_of_linkCertificate` and the
rational Gram factor built above: no analytic step, no literature input, and no
eigenvalue estimate is left. -/
theorem hasKazhdanPropertyT_of_linkData
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Nonempty Generator] [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (D : BipartiteLinkData (Generator × Bool)) (d : ℕ)
    (hdeg : ∀ u, TriangularHodgeLayer.degree T u = d)
    (hdegval : (d : ℚ) = D.deg)
    (hadj : ∀ u v, (TriangularHodgeLayer.adjacencyCount T u v : ℚ) = D.adj u v) :
    HasKazhdanPropertyT.{0, 0} (TriangularHodgeLayer.Presented T) :=
  TriangularHodgeLayer.presented_hasKazhdanPropertyT_of_linkCertificate T d
    D.gapValue D.gramRow (linkCertificateChecks_of_linkData T D d hdeg hdegval hadj)

/-- **A triangular presentation whose link is the incidence graph of a
projective plane has property `(T)`.**  The specialization that carries the
mathematics: the hypothesis is a finite incidence table and a count of cyclic
corners, and the conclusion is Kazhdan's property for the presented group. -/
theorem hasKazhdanPropertyT_of_projectivePlaneLink
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Nonempty Generator] [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Pl : ProjectivePlaneData Generator) (d : ℕ)
    (hdeg : ∀ u, TriangularHodgeLayer.degree T u = d)
    (hdegval : (d : ℚ) = Pl.order + 1)
    (hadj : ∀ u v, (TriangularHodgeLayer.adjacencyCount T u v : ℚ) = Pl.linkAdj u v) :
    HasKazhdanPropertyT.{0, 0} (TriangularHodgeLayer.Presented T) :=
  hasKazhdanPropertyT_of_linkData T Pl.linkData d hdeg hdegval hadj

end KazhdanHyp
end GroupApproximation
