---
rg: 2
id: sl2-subfield-root-links-codistance-large-q-proof
kind: route
title: Girth 10 fixes the eighth moment of the link spectrum, and every nontrivial eigenvalue has multiplicity at least q^2 - 1
target: sl2-subfield-root-links-codistance-large-q
requires: [coset-graph-singular-values-bound-fixed-space-angles, sl2-subfield-root-pair-girth-eight]
---

Let `A = SL_2(F)` with `Q = q^2`, `E = u(k)`, `E' = v(sk)`, and `T = MM^T/q^2` on `ℓ^2(A/E)`.

**1. Minimal degree.** Every nontrivial irreducible complex representation `π` of `A` has
`dim π >= Q - 1`.
- `A` is simple (`Q >= 4`). If `U = u(F)` acted trivially, `ker π` would contain the normal closure of
  `U`, which is `A`, and `π` would be trivial.
- So `π|_U` contains a nontrivial character `ψ_a(u(x)) = χ(ax)`, `a ≠ 0`.
- `diag(t, t^{-1})` conjugates `u(x)` to `u(t^2 x)`, so `π(diag(t,t^{-1}))` carries the `ψ_a`-isotypic
  space onto the `ψ_{a t^{±2}}`-isotypic space.
- Squaring is onto `F^*`, so all `Q - 1` nontrivial characters occur, and `dim π >= Q - 1`.

**2. Multiplicity.** By Step 2 of `coset-graph-singular-values-bound-fixed-space-angles-proof`, `T` is
`R_E R_{E'} R_E` on `ℓ^2(A)^E = ⊕_π π ⊗ (π^*)^E`, acting as `1 ⊗ (·)`.
- Every eigenvalue contributed by `π` has multiplicity at least `dim π`.
- The constants are the only contribution of the trivial `π`.
- So the eigenvalue `σ_2^2` (the largest from a nontrivial `π`) has multiplicity at least `q^2 - 1`,
  and `tr(T^4) >= 1 + (q^2 - 1) σ_2^8`.

**3. The eighth moment.** `A` acts transitively on `A/E` by graph automorphisms, so
`tr(T^4) = n W_8 / q^8`, where `W_8` counts closed walks of length 8 at one vertex.
- By `sl2-subfield-root-pair-girth-eight` (b), the girth is at least `10`, so the ball of radius 4 is a
  tree and `W_8 = T_8(q)`.
- **Tree count.** In the `d`-regular tree, the walks from a child back to itself inside its branch have
  generating function `C(x) = Σ_j Cat_j (d-1)^j x^j`, with `x` marking two steps. The closed walks at the
  root have generating function `1/(1 - d x C(x))`.
- With `c = d - 1` the coefficient of `x^4` is `5dc^3 + 5d^2c^2 + 3d^3c + d^4`. That equals
  `14d^4 - 28d^3 + 20d^2 - 5d`, which checks as `70` for `d = 2`.

**4. The bound.** Combining Steps 2 and 3,
`σ_2^8 <= (n T_8(q)/q^8 - 1)/(q^2 - 1)`.
- Since `n = q(q^4 - 1) <= q^5` and `T_8(q) <= 14q^4`, the numerator is at most `14q - 1`.
- So `σ_2^8 < 14q/(q^2 - 1)`.
- Bernoulli gives `(1 - 2/q)^8 >= 1 - 16/q`.
- `14q/(q^2 - 1) < 1 - 16/q` iff `q^3 - 30q^2 - q + 16 > 0`. This holds at `q = 32` (value `2032`), and
  the cubic is increasing for `q >= 32`, since its derivative `3q^2 - 60q - 1 > 0` there.

Hence `σ_2 < 1 - 2/q` for every `q = 2^f >= 32`.

**5. Connectivity and angles.** If `Γ_s` were disconnected, a nontrivial `π` would contribute the
eigenvalue `1`, so `σ_2 = 1`, contradicting Step 4. So `<E, E'> = A`. The angle statement is
`coset-graph-singular-values-bound-fixed-space-angles` (2). ∎
