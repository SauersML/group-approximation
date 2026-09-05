# `ℂP^n` foundations: published signatures (lane `found-cpn-cohomology`)

Owner: lane `found-cpn-cohomology`.
Files owned: `GroupApproximation/AlgTop/ComplexProjective*.lean`.
Consumers: `found-chern-classes`, `found-ktheory-bott`, `found-mapping-torus-parity`,
`lix-spaces`, `lix-clutching`, `lix-obstruction`.

Target: manuscript
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md` §2,
equation (2.1),

```
H^*(Y; Z) = Z[h_1,...,h_l]/(h_1^{d_1+1},...,h_l^{d_l+1}),  |h_j| = 2,  Y = prod_j CP^{d_j}
c_m(H) = prod_j h_j^{d_j},   |<c_m(H), [Y]>| = 1.
```

Everything is stated in the concrete projection model — no quotient topology, no bundle
theory.

## Part A — authored, no dependency on any other lane

Namespace `GroupApproximation.AlgTop`, all in `GroupApproximation/AlgTop/`.

### A.0 The model (`ComplexProjectiveBasic.lean`)

```lean
def IsLineProj {n : Type*} [Fintype n] (q : Matrix n n ℂ) : Prop :=
  qᴴ = q ∧ q * q = q ∧ q.trace = 1

def CP (d : ℕ) : Type :=
  {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ // IsLineProj q}

def CP.mat (x : CP d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := x.1
theorem CP.prop (x : CP d) : IsLineProj x.mat
```

`CP d` is complex projective `d`-space: `CP 0` is a point, `CP d` has real dimension
`2d`. **Do not change this indexing**; every cohomology statement below is keyed to it.

Instances: `TopologicalSpace (CP d)` (subspace of the product topology on matrices),
`T2Space (CP d)`, `CompactSpace (CP d)`, `Nonempty (CP d)`.

Key algebra, all elementary (no trace-equals-rank theorem, no spectral theorem):

```lean
theorem IsLineProj.conj_entry (h : IsLineProj q) (a b : n) : conj (q a b) = q b a
theorem IsLineProj.sum_mul (h : IsLineProj q) (x y : n) : (∑ c, q x c * q c y) = q x y
theorem IsLineProj.diag_eq (h : IsLineProj q) (j : n) :
    q j j = ((∑ c, Complex.normSq (q c j) : ℝ) : ℂ)
theorem IsLineProj.sum_normSq_eq_one (h : IsLineProj q) :
    (∑ j, ∑ c, Complex.normSq (q c j)) = 1
theorem IsLineProj.norm_entry_le_one (h : IsLineProj q) (a b : n) : ‖q a b‖ ≤ 1
theorem IsLineProj.col_eq_zero_of_diag_eq_zero
    (h : IsLineProj q) {j : n} (hj : q j j = 0) (c : n) : q c j = 0
theorem IsLineProj.row_eq_zero_of_diag_eq_zero
    (h : IsLineProj q) {j : n} (hj : q j j = 0) (c : n) : q j c = 0

/-- rank-one normal form, as the vanishing of every 2x2 minor -/
theorem IsLineProj.minor (h : IsLineProj q) (a b j : n) : q a j * q j b = q j j * q a b
theorem IsLineProj.eq_colProj (h : IsLineProj q) {j : n} (ht : q j j ≠ 0) : q = colProj q j
```

`IsLineProj.minor` is the single fact every downstream computation runs on. Its proof:
`colProj q j` (entries `q a j * q j b / q j j`) is a self-adjoint idempotent of trace one
with `q * colProj q j = colProj q j * q = colProj q j`, so `q - colProj q j` is a
self-adjoint idempotent of trace `0`; and for a self-adjoint idempotent `r`,
`trace r = ∑_{a,c} ‖r c a‖²`, so `trace r = 0` forces `r = 0`.

Constructors: `CP.ofVec v hv` for `∑ a, Complex.normSq (v a) = 1`; `CP.basePoint d`.
Continuity: `CP.continuous_val`, `CP.continuous_entry a b`.

### A.1 The affine chart (`ComplexProjectiveChart.lean`)

```lean
def CP.chartVec (w : Fin d → ℂ) : Fin (d + 1) → ℂ := Fin.cons 1 w
def CP.chartAt (w : Fin d → ℂ) : CP d          -- [1 : w₁ : ... : w_d]
def CP.chartInv (x : CP d) : Fin d → ℂ         -- fun i => x.mat i.succ 0 / x.mat 0 0
def CP.chartSet (d : ℕ) : Set (CP d) := {x | x.mat 0 0 ≠ 0}

theorem CP.isOpen_chartSet : IsOpen (chartSet d)
theorem CP.chartInv_chartAt (w : Fin d → ℂ) : chartInv (chartAt w) = w
theorem CP.chartAt_chartInv (x : CP d) (hx : x.mat 0 0 ≠ 0) : chartAt (chartInv x) = x
def CP.chartHomeo (d : ℕ) : (Fin d → ℂ) ≃ₜ ↥(chartSet d)
```

No square roots: the chart normalizes by the *squared* norm, which is exactly what the
idempotent law asks for, so the chart map is rational in `w` and `conj w`.

### A.2 The hyperplane (`ComplexProjectiveHyperplane.lean`)

```lean
def CP.incl (x : CP d) : CP (d + 1)                    -- pad by a zero row and column
theorem CP.continuous_incl : Continuous (incl (d := d))
theorem CP.injective_incl : Function.Injective (incl (d := d))
theorem CP.isClosedEmbedding_incl : Topology.IsClosedEmbedding (incl (d := d))
theorem CP.range_incl : Set.range (incl (d := d)) = {y : CP (d + 1) | y.mat 0 0 = 0}
theorem CP.chartSet_eq_compl_range_incl :
    chartSet (d + 1) = (Set.range (incl (d := d)))ᶜ
```

So `CP^{d+1}` is the disjoint union of the open `2(d+1)`-cell `chartSet (d+1)` (which is
homeomorphic to `ℂ^{d+1}`) and the closed subspace `CP^d`. Iterating gives the even-cell
filtration `CP^0 ⊂ CP^1 ⊂ ... ⊂ CP^n` with **exactly one cell in each even dimension
`0, 2, ..., 2n` and none in odd dimensions** (mandate item 1), which is what
`found-ktheory-bott` needs for `K^0(CP^n)`.

Because every cell is even-dimensional, every cellular boundary map of `CP^n` is a map
between a free group and `0`, hence zero; the cellular chain complex has zero
differential. That is why `CP^n` is far cheaper than the `RP^n` precedent in
`GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/`.

## Part B — signatures that consume `found-cohomology-ring`

Notation: `H n X` for integral singular cohomology in degree `n`. The real name is
whatever `found-cohomology-ring` publishes; these statements are written against the
*shape* `H n X : AddCommGrp` (or `ModuleCat ℤ`), contravariant in `X`, with a graded cup
product and a Kunneth isomorphism. **The only thing that can change below is the name
`H`, not the mathematical content.**

### B.1 Item 2 — additive cohomology of `CP^d`

```lean
theorem CP.cohomology_even_iso (d k : ℕ) (hk : k ≤ d) : Nonempty (H (2 * k) (CP d) ≃+ ℤ)
theorem CP.cohomology_odd_isZero (d j : ℕ) (hj : Odd j) : Subsingleton (H j (CP d))
theorem CP.cohomology_high_isZero (d j : ℕ) (hj : 2 * d < j) : Subsingleton (H j (CP d))
```

Proof route (fixed; it is the route the `RP^n` precedent uses): reduced Mayer-Vietoris
for the open cover `U = chartSet d`, `V = {x | x ≠ basePoint d}` of `CP d`, with

* `U ≅ ℂ^d` contractible (`CP.chartHomeo`);
* `V ≃ CP^{d-1}` (deformation retraction, Part C below);
* `U ∩ V ≅ ℂ^d \ {0} ≃ S^{2d-1}`.

Then `H~^k(CP^d) ≅ H~^k(CP^{d-1})` for `k ≤ 2d-2`, `H~^{2d-1}(CP^d) = 0`, and
`H~^{2d}(CP^d) ≅ H~^{2d-1}(S^{2d-1}) ≅ ℤ`.

### B.2 Item 3 — the ring `Z[h]/(h^{d+1})`

```lean
def CP.h (d : ℕ) : H 2 (CP d)                              -- the degree-2 generator
theorem CP.h_pow_ne_zero (d k : ℕ) (hk : k ≤ d) : CP.h d ^ k ≠ 0
theorem CP.h_pow_spans (d k : ℕ) (hk : k ≤ d) (c : H (2 * k) (CP d)) :
    ∃ m : ℤ, c = m • (CP.h d ^ k)
theorem CP.h_pow_succ_eq_zero (d : ℕ) : CP.h d ^ (d + 1) = 0
theorem CP.incl_h (d : ℕ) : (CP.incl (d := d))^* (CP.h (d + 1)) = CP.h d
def CP.cohomologyRingEquiv (d : ℕ) :
    (⨁ j, H j (CP d)) ≃+* (Polynomial ℤ ⧸ Ideal.span {Polynomial.X ^ (d + 1)})
```

`CP.incl_h` (restriction along the hyperplane inclusion sends the generator to the
generator) is the load-bearing step: the induction on `d` is "restrict `h^k` from `CP^d`
to `CP^k` and land on the top class", and it needs **naturality of the cup product**,
which is the one thing I asked `found-cohomology-ring` to guarantee.

`CP.h` will later be identified with `c₁` of the tautological line
(`found-chern-classes`); that identification is a separate theorem and this lane does not
block on it.

### B.3 Item 4 — products, and (2.1)

```lean
/-- `Y = prod_j CP^{d_j}`. -/
abbrev CPProd {ι : Type} [Fintype ι] (dd : ι → ℕ) : Type := ∀ j : ι, CP (dd j)

instance : CompactSpace (CPProd dd)
instance : T2Space (CPProd dd)

/-- `h_j`, pulled back from the `j`-th factor. -/
def CPProd.h {ι : Type} [Fintype ι] (dd : ι → ℕ) (j : ι) : H 2 (CPProd dd)

/-- the top monomial `prod_j h_j^{d_j}` in degree `2m`, `m = sum_j d_j` -/
def CPProd.topClass {ι : Type} [Fintype ι] (dd : ι → ℕ) :
    H (2 * ∑ j, dd j) (CPProd dd) := ∏ j, (CPProd.h dd j) ^ (dd j)

theorem CPProd.cohomology_top_iso {ι : Type} [Fintype ι] (dd : ι → ℕ) :
    Nonempty (H (2 * ∑ j, dd j) (CPProd dd) ≃+ ℤ)
theorem CPProd.topClass_ne_zero {ι : Type} [Fintype ι] (dd : ι → ℕ) :
    CPProd.topClass dd ≠ 0
theorem CPProd.topClass_spans {ι : Type} [Fintype ι] (dd : ι → ℕ)
    (c : H (2 * ∑ j, dd j) (CPProd dd)) : ∃ m : ℤ, c = m • CPProd.topClass dd
theorem CPProd.cohomology_odd_isZero {ι : Type} [Fintype ι] (dd : ι → ℕ) (n : ℕ)
    (hn : Odd n) : Subsingleton (H n (CPProd dd))
theorem CPProd.cohomology_free {ι : Type} [Fintype ι] (dd : ι → ℕ) (n : ℕ) :
    Module.Free ℤ (H n (CPProd dd))
```

`CPProd.topClass_spans` together with `CPProd.topClass_ne_zero` **is** the content of
(2.1): the top monomial generates `H^{2m}(Y;Z) ≅ Z`, so its pairing with the fundamental
class is a unit, i.e. `±1`. If `found-cohomology-ring` supplies a fundamental class and a
Kronecker pairing I will additionally state

```lean
theorem CPProd.pairing_topClass {ι : Type} [Fintype ι] (dd : ι → ℕ) :
    pairing (CPProd.topClass dd) (fundamentalClass (CPProd dd)) = 1 ∨
    pairing (CPProd.topClass dd) (fundamentalClass (CPProd dd)) = -1
```

but the generator form is what Lemma 3 actually consumes, and it needs no fundamental
class at all — a simplification of the manuscript worth taking.

### B.4 Item 5 — products with spheres (torsion-freeness)

```lean
-- `Sph n := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`
abbrev LIXBase {ι : Type} [Fintype ι] (dd : ι → ℕ) : Type := Sph 1 × Sph 5 × CPProd dd

theorem LIXBase.cohomology_free {ι : Type} [Fintype ι] (dd : ι → ℕ) (n : ℕ) :
    Module.Free ℤ (H n (LIXBase dd))
theorem LIXBase.cohomology_finite {ι : Type} [Fintype ι] (dd : ι → ℕ) (n : ℕ) :
    Module.Finite ℤ (H n (LIXBase dd))
```

`Module.Free ℤ M` for finitely generated `M` is exactly torsion-freeness, which is what
the manuscript's Lemma 3 uses to identify the integral coefficients from a rational
computation. Everything is free on both sides, so the Kunneth isomorphism is clean and
multiplicative and this is a corollary rather than a separate argument.

Downstream (`found-mapping-torus-parity`) also needs the *explicit basis*: monomials
`t^{e0} x^{e1} prod_j h_j^{b_j}` with `e in {0,1}`, `b_j ≤ d_j`. That is the
multiplicative Kunneth statement in B.3 tensored with `H^*(S^1) ⊗ H^*(S^5)`, and I will
state it as an explicit `Basis` once the Kunneth API name is fixed.

## Part C — the remaining unconditional point-set input I still owe

The Mayer-Vietoris route needs one more purely point-set fact, which no other lane owns
and which needs no cohomology:

```lean
/-- `CP^{d+1}` minus the base point deformation retracts onto the hyperplane `CP^d`. -/
def CP.punctureRetract (d : ℕ) :
    ContinuousMap.HomotopyEquiv ↥{y : CP (d + 1) | y ≠ basePoint (d + 1)} (CP d)
```

Construction (concrete, in the projection model): for `y ≠ basePoint`, `y.mat 0 0 < 1`,
so with `δ t = Fin.cons (1 - t) 1 : Fin (d+2) → ℝ` the number
`τ t y = ∑ c, (δ t c)^2 * y.mat c c` satisfies `τ ≥ 1 - y.mat 0 0 > 0`, and

```
(H t y).mat a b = δ t a * y.mat a b * δ t b / τ t y
```

is again a rank-one projection — the idempotent law follows from `IsLineProj.minor`
applied twice, with no rank theorem. `H 0 = id`, `H 1` lands in `range incl`, and `H t`
fixes `range incl` pointwise. This is the attaching-structure half of mandate item 1.

## What I need, restated

From `found-cohomology-ring`, in priority order: (1) the Z-coefficient cohomology
functor's name; (2) homotopy invariance in homotopy-equivalence form; (3) **reduced**
cohomology and the reduced Mayer-Vietoris exact sequence for an open cover;
(4) `H^*(S^n;Z)` with a named generator; (5) cup product with naturality; (6) Kunneth in
multiplicative form for free, degreewise finitely generated cohomology.

Items (1)-(4) unblock B.1; (5) unblocks B.2; (6) unblocks B.3 and B.4.
