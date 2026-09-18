---
rg: 2
id: nv-local-density-walls-bounded-on-callard-salo-element
kind: claim
title: "Integrated local walls on C^n with subexponential germ density (anisotropy walls, cocycle integrals, Lebesgue-integrated wall counts) are bounded on the Callard--Salo element, so none is proper modulo T_n"
distinct_from:
  brin-thompson-nv-no-cubical-action-proper-mod-triangular: that kills commensurating actions (a single discrete wall space) through the bounded-or-linear dichotomy; this kills non-cubical measured walls integrated over C^n, which escape that dichotomy, through local periodicity of f and the belt-length tail
  brin-thompson-nv-cnd-proper-modulo-triangular-subgroup: that is the open existence claim; this is an obstruction to one class of candidates for it
  callard-salo-element-is-ae-locally-periodic: that is the dynamical input about f; this is its consequence for cnd functions
---

**Statement.** Let `n ≥ 2`, `λ` the Lebesgue measure on `C^n`, and `f ∈ nV` the Callard–Salo
element. For `g ∈ nV` and `x ∈ C^n`, let `r(g,x)` be the least total address length of a brick
`B ∋ x` on which `g` is canonical, plus that of `gB`. Call a function `ψ ≥ 0` on a subgroup
`G ≤ nV` containing `f` a *local density wall function* if

  `ψ(g) ≤ A + ∫_{C^n} Φ(r(g,x)) h(x) dλ(x)` for all `g ∈ G`,

where `h ≥ 0` is bounded and `Φ : N → [0,∞)` is nondecreasing and subexponential. Here
subexponential means `Σ_ℓ (ℓ+1) q^ℓ Φ(C(ℓ+1)) < ∞` for the constants `C, q` of
`callard-salo-element-is-ae-locally-periodic`; every polynomial `Φ` qualifies. Then
`sup_N ψ(f^N) < ∞`. Consequently no such cnd function is proper modulo `T_n`, or modulo any
undistorted subgroup, and none is proper.

**Members of the class.** Each of the following is a local density wall function.
- The *anisotropy wall* on the area-preserving subgroup of `2V`. Its walls are `A = C^2 × {k ≥ 0}` in
  the Maharam-type extension `C^2 × Z`, with `(x,k) ↦ (gx, k + α(g,x))`, where `α = c_1 = −c_2`. Its
  wall function is `ψ(g) = ∫|α(g,x)| dx`, which is cnd, because it is `‖1_{gA} − 1_A‖²` in
  `L²(C^2×Z)`. Callard–Salo's `f` lies in this subgroup when the codes `C, D` of `lem:TMin2V` are
  block codes (`n` a power of 2).
- Every integrated cocycle function `∫ Φ(|c(g,x)|) dλ` with polynomial `Φ`.
- Every Lebesgue-integrated family of wall counts `ψ(g) = ∫ ψ_x(g) dλ(x)` in which the local wall
  count at `x` is at most polynomial in the size of the germ of `g` at `x`. Examples are Farley-type
  counts in a chart of bounded depth around `x`, or finitely many half-space counts of the exponent
  cocycle.
- More generally, every measured-wall structure `(Ω, μ)` over `C^n` whose fibre over `x` has mass
  at most `h(x)·Φ(size of the relevant germ)`.

**Invariant and death step.** The invariant is the belt-length tail `λ(L ≥ ℓ) ≤ C(ℓ+1)q^ℓ`,
set against the uniform germ bound `r(f^N,x) ≤ C(L(x)+1)`. Every member dies at the same step:

  `ψ(f^N) ≤ A + ‖h‖_∞ Σ_ℓ λ(L=ℓ) Φ(C(ℓ+1)) < ∞`, uniformly in `N`.

Then the powers `f^N` lie in pairwise distinct cosets of `T_n`
(`brin-thompson-nv-no-cubical-action-proper-mod-triangular`, item 2). So a bounded function cannot
be proper modulo `T_n`.

**Forced shape (what survives).** For a cnd `ψ = ∫ φ(g,x) dμ` built fibrewise over `C^n`,
unbounded growth along `f` needs `Σ_ℓ λ(L=ℓ) sup_N φ(f^N,·)|_{L=ℓ} = ∞`. The region `{L = ℓ}`
has mass about `q^ℓ`, and there `f` has period `exp(Θ(ℓ))`. So the weight on `{L = ℓ}` must grow
exponentially in `ℓ`: exponentially in germ size, not polynomially. A contribution of order 1 from
each region `{L = ℓ}` with `ℓ ≲ log N` gives `ψ(f^N) ≍ log N`, which is well inside `O(log^8 N)`.
The only natural source of such weights is the Radon–Nikodym factor `2^{Σ t}` of the Maharam
extension `C^n × Z^n` with its infinite invariant measure. That extension must use fibre heights
`|t| ≍ L`, and it must not be fibre-constant, since fibre-constant commensurated sets give bounded
wall counts. The transversal half of the triangular split is thus pushed into infinite-measure
Maharam walls, weighted like an odometer.

## Attempts

- 2026-09-17 (e-nv-walls, swarm-0917). *Proof of the reduction; OPEN only through its input.*
  - **Given** items 1 and 3 of `callard-salo-element-is-ae-locally-periodic`: for a.e. `x`,
    `r(f^N,x) ≤ C(L(x)+1)` for all `N`. Since `Φ` is nondecreasing,
    `ψ(f^N) ≤ A + ‖h‖_∞ ∫ Φ(C(L+1)) dλ = A + ‖h‖_∞ Σ_ℓ λ(L=ℓ) Φ(C(ℓ+1))`. This is finite by
    item 1 and the subexponential hypothesis, and does not depend on `N`.
  - **Members.**
    - Anisotropy wall: `|α(g,x)| ≤ r(g,x)`, `h = 1`, `Φ(r) = r`.
    - Cocycle integrals: `|c(g,x)| ≤ r(g,x)`.
    - Integrated wall counts: bounded by hypothesis.
  - **Coset separation** is item 2 of `brin-thompson-nv-no-cubical-action-proper-mod-triangular`,
    which is ESTABLISHED.
  - This claim becomes ESTABLISHED when `callard-salo-element-is-ae-locally-periodic` does.
- *Secondary death of the anisotropy wall.* The level-preserving locally finite subgroup of
  equal-shape brick permutations has `c ≡ 0`, so `ψ` vanishes on it. Two further failures:
  - Non-area-preserving elements do not preserve `λ⊗counting` on `C^2 × Z`. Extending to them by the
    Maharam weight on volume `s` forces the commensurated sets to have finite fibre mass, and the
    wall count becomes bounded.
  - Fibre-constant sets `A_x = S` give bounded wall counts.
  These are recorded as sketches, not proved here.
- *Growth computation (the assignment's falsifiable step).* The assignment expected
  `ψ(f^N) = 2E|D_N|` (head displacement) with `O(log N)` growth. Actually `ψ(f^N)` is bounded,
  with `E[L+1] = 4` for the uniform one-head `RTM(18,96)` model: the head is confined to its
  conveyor belt. The distortion of `f` lives in its word norm, not in how far points move.
  `experiments/nv-measured-walls-2026-09-17/smart_belt_periods.py` records the belt periods
  `2c·3^c`.
