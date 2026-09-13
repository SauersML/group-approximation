---
rg: 2
id: determinant-conjecture-gives-full-atiyah-base-change
kind: claim
title: A torsion-free group with Strong Atiyah over the algebraic numbers and the determinant conjecture satisfies Strong Atiyah over C
distinct_from:
  strong-atiyah-base-change-algebraic-to-complex: that asks whether Strong Atiyah over Qbar for all torsion-free groups gives it over C, with no determinant hypothesis; this asks it group by group under the determinant conjecture, where transcendence degree one is already proved.
  atiyah-base-change-in-transcendence-degree-one-under-det: that is the established case of coefficient fields of transcendence degree at most one; this is the full statement, open from transcendence degree two.
  strong-atiyah-base-change-from-galois-invariance: that derives the conclusion from full Galois invariance; this asks for it from the determinant conjecture, which gives invariance only in transcendence degree one so far.
artifacts:
  - research/artifacts/atiyah-transcendence-degree-one-base-change-2026-09-13.md
---

**OPEN.** Let `G` be torsion-free and satisfy Strong Atiyah over `Qbar` and
Lueck's determinant conjecture. Then every matrix over `C[G]` has integral von
Neumann kernel dimension.

**Known part.** Coefficient fields of transcendence degree at most one
([[atiyah-base-change-in-transcendence-degree-one-under-det]]). By
`atiyah-base-change-holds-off-a-countable-set`, in several variables the
exceptional parameter set is a Borel, null, meagre set, so what remains is that
set being empty.

**Why it matters.** Through `algebraic-atiyah-and-determinant-one-group-tester`,
this claim together with `SA(E)` and `Det(E)` for the master host proves the root
`strong-atiyah-torsion-free`. That is the route
`strong-atiyah-torsion-free-via-master-host-determinant`. The complex Strong
Atiyah conjecture would then be two statements about one group.

## Attempts

(Details in the artifact, Section 9.)

* **Kronecker product of companion pencils.** Dies on distances. It gives an
  integral model with
  `Delta = |a_1|^(N d_2) |a_2|^(N d_1) prod_(j,k) Delta(M(alpha_j, beta_k))`.
  But `prod_(j,k) dist((alpha_j, beta_k), z)` has no product formula in
  `p_1(z_1)` and `p_2(z_2)`. Only the nearest block gains, while the loss is
  `N (d_2 log M(p_1) + d_1 log M(p_2))`.
* **u-resultants and Chow forms of zero-dimensional schemes.** Not attempted in
  full. Minkowski's gain in `s` variables grows like `n^s log H`, and the
  arithmetic Bezout loss like `N s n^(s-1) log H`, so the exponents close. The
  missing input bounds `prod_(zeta in V) ||zeta - z||` by polynomial values, which
  needs transversality control. That is the Nesterenko--Philippon elimination
  machinery.
* **Rational functions of one coordinate.** Dies. Approximating `z_2` by `r(z_1)`
  and restricting to the curve `x_2 = r(x_1)` brings in the Lipschitz constant of
  `r` at each root, and balancing degrees does not close.
* **Continuity along subvarieties.** Dies. The curve argument needs a finite map
  to a base with constant fibre sums. A point of transcendence degree 2 lies on
  no curve defined over `Qbar`.
* **Central variables.** Dies at almost-everywhere. For `G x Z` the one-variable
  theorem gives `integral_T (k(z_1, omega) - g_0) d omega = 0` with a nonnegative
  integrand. So the excess vanishes for almost every `omega`, not at a chosen
  point.
* **Lelong-number analytic sets (Siu).** Dies at algebraicity of analytic sets.
  - `U(x) = log Delta(M(x_1, x_2))` is plurisubharmonic. At a point with kernel
    excess `kappa` it satisfies `U(w) <= kappa log ||w - z|| + C` nearby, so its
    Lelong number there is at least `kappa`. By Siu's theorem (Invent. Math. 27
    (1974)) the sets `{nu_U >= c}` are closed analytic subvarieties of `C^2`, and
    the exceptional points lie in them.
  - Restricted to a Qbar-line that is not a jump line, the proof of
    `determinant-conjecture-gives-one-variable-atiyah-base-change` runs verbatim
    with the Lelong number of `log Delta` in place of the kernel dimension. So
    Lelong numbers vanish at transcendental points of such lines, and
    `{nu_U >= c}` meets generic Qbar-lines only in algebraic points.
  - That does not make the components algebraic. A transcendental analytic curve
    can meet every algebraic line only at algebraic points, as in Staeckel-type
    constructions. Pushing algebraic points of degree `d` towards a transcendental
    curve by Dirichlet counting gives distance about `H^(-d)`, which is only the
    order of the loss `N d log H` from the conjugates.
* **Iterated resultants over `Z[x_1]`.** Dies at transcendence measures.
  - The companion model of `p in Z[x_2]` is an integral family `X(x_1)` in `x_1`.
    The one-variable argument at `z_1` would need
    `log Delta(X(z_1)) >= -o(n log H)`, with `n = deg p` and `H = H(p)`.
  - For `G = 1` this is a lower bound for the resultant polynomial
    `Res_(x_2)(p, det M)` at `z_1`. Even for numbers with a transcendence measure
    it is only `-C N d (N d + log H)`, already the size of the gain.
  - So the one-variable determinant bound cannot be iterated one coordinate at a
    time. A proof needs genuinely two-dimensional elimination, with products of
    distances over zero-dimensional schemes (Nesterenko--Philippon).
