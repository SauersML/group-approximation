---
rg: 2
id: rational-slope-germ-groups-have-bs-but-no-heisenberg-proof
kind: route
title: Slope homomorphism, periodic dilations, and a component count against the slope
target: rational-slope-germ-groups-have-bs-but-no-heisenberg
requires: []
---

Germs are at `+∞`. "`φ` is `(q,r)`" means `φ(y+q) = φ(y) + r` for large `y`.

**Item 1.**
- **Closure.** If `φ` is `(q,r)` and `ψ` is `(q',r')`, then `φψ` is `(qq', rr')`:
  `φψ(y + qq') = φ(ψ(y) + r'q) = φψ(y) + rr'`. Also `φ^-1` is `(r,q)`.
- **Well-defined slope.** If `φ` is both `(q,r)` and `(q',r')`, then
  `φ(y) + rq' = φ(y + qq') = φ(y) + r'q`, so `r/q = r'/q'`. The computation above shows
  `λ` is a homomorphism.
- **Onto.** Given `q, r ≥ 1`, choose an increasing PL₂ homeomorphism `[0,q] → [0,r]`.
  To build one, subdivide both intervals into standard dyadic intervals `[k/2^n,
  (k+1)/2^n]`, halving pieces until the two counts agree, and map the pieces affinely in
  order. Extend it by `φ(y + kq) = φ(y) + kr`.
- **Kernel.** `λ(φ) = 1` means `φ` is `(q,q)`, i.e. commutes with `z^q` near `+∞`. Such a
  germ extends uniquely to an element of `C(z^q)`. The union is directed because
  `C(z^q) ∪ C(z^q') ⊆ C(z^(qq'))`.
- **`C(z^q) ≅ T̄`.** Take the PL₂ homeomorphism `k` with `k(y + q) = k(y) + 1` built from
  a PL₂ map `[0,q] → [0,1]`. Then `k z^q k^-1 = z`, and conjugation by `k` maps
  `C(z^q)` onto `C(z) = T̄`.
- **Torsion-free.** If a germ `g ≠ 1` of an increasing map has `g(y) > y` for some large
  `y` (or `<`), then `g^n(y) > y` for all `n`.

**Item 2.** Let `δ = δ_m` be a `(1,m)` element from item 1. Then `δ z = z^m δ`, i.e.
`δ z δ^-1 = z^m`. Put `u_k = δ^-k z δ^k`. Then `u_(k+1)^m = u_k`, so the `u_k` generate
a nested union of infinite cyclic groups inside `K`. By torsion-freeness it is ≅ `Z[1/m]`,
and `z ≠ 1` maps to `1`. Since `λ(δ) = m` has infinite order, `⟨δ⟩ ∩ K = 1`. So the map
`BS(1,m) = Z[1/m] ⋊ Z → E` is injective.

**Item 3.**
- **Setup.** Let `x, y ∈ E` and let `c = [x,y] ≠ 1` commute with `x` and `y`. Every
  nonabelian nilpotent group contains such a triple: take `y` in the second centre and
  not central. `λ(c) = 1`, so `c ∈ K`.
- **Case λ(x) = λ(y) = 1.** Then `x, y ∈ C(z^q) ≅ T̄` for one `q`. Every nilpotent
  subgroup of `T̄` is abelian; artifact §3, Lemma D2. Alternatively, `T̄ ≤ VA` together
  with O4: `[x^n, y^n] = c^(n²)` would make `c` distorted. So `c = 1`, a contradiction.
- **Case λ(x) = μ ≠ 1** (otherwise swap the roles of `x` and `y`).
  - **Translation number.** `c` extends to an element of some `C(z^q)`. Let `τ(c)` be its
    translation number, with `|c^n(w) − w − nτ(c)| ≤ q` for all `w`. From `x` being
    `(q',r')`, `x(w + t) = x(w) + μt + O(1)` for large `w`. Then
    `x c x^-1 = c` gives `τ(c) = μ τ(c)`, so `τ(c) = 0`.
  - **Components.** A lift commuting with `z^q` with translation number `0` has a fixed
    point. So `Fix(c)` is nonempty, closed and `z^q`-invariant.
  - `c ≠ 1` is PL₂ with finitely many breakpoints per period. So `supp(c)` is a nonempty
    `z^q`-periodic union of open intervals, with `N ≥ 1` of them per period, each of
    length at most `q`.
  - `x` commutes with `c` near `+∞`, so it maps components of `supp(c)` far out
    bijectively onto components far out.
  - **Count.** `[Y, Y + Mq')` contains `N M q'/q + O(1)` components. Its image
    `[x(Y), x(Y) + M r')` contains `N M r'/q + O(1)` components.
  - Equality for all large `M` forces `r' = q'`, i.e. `μ = 1`. Contradiction.
