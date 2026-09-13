---
rg: 2
id: determinant-conjecture-excludes-liouville-atiyah-exceptions
kind: claim
title: Under the determinant conjecture, complex Strong Atiyah exceptions are badly approximable transcendental numbers
distinct_from:
  atiyah-base-change-holds-off-a-countable-set: that makes the exceptional set countable using only Strong Atiyah over the algebraic numbers; this uses the determinant conjecture to keep every exceptional point a quantitative distance away from algebraic numbers of bounded degree.
  serre-class-atoms-obey-degree-bound: that excludes transcendental atoms of one self-adjoint integral matrix through integer polynomials in the operator; this controls kernels of polynomial families at a transcendental parameter through algebraic approximants of the parameter.
  algebraic-atiyah-and-determinant-one-group-tester: that transports Strong Atiyah over the algebraic numbers together with the determinant conjecture from the master host to all torsion-free groups, and records nothing over C; this is a complex-coefficient consequence of that conjunction.
artifacts:
  - research/artifacts/atiyah-liouville-base-change-2026-09-12.md
---

**ESTABLISHED** by [[liouville-atiyah-exceptions-proof]].

**Setting.**
* `G` is torsion-free and satisfies Lueck's determinant conjecture and Strong
  Atiyah over `Qbar`.
* `A(x)` is a matrix over `O_F[x][G]`, for a number field `F`, with `n` columns
  and degree `D` in `x`.
* `r(A)` is its rank over `D_(Qbar[G])(x)`, and
  `kappa(z) = dim ker A(z) - (n - r(A)) >= 0`.

**Statements.**
1. Only finitely many algebraic `xi` have `kappa(xi) != 0`.
2. For a transcendental `z_0` with `kappa(z_0) > 0` and every `d`, there are
   constants `c, C > 0` such that

   ```text
   |z_0 - xi|  >=  c * H(xi)^(-C / kappa(z_0))       for all algebraic xi with [Q(xi):Q] <= d,
   ```

   where `H` is the naive height of the minimal polynomial.
3. The countable exceptional set `E_G` of
   `atiyah-base-change-holds-off-a-countable-set` contains no algebraically
   Liouville number: no transcendental number that algebraic numbers of some
   bounded degree approximate faster than every power of their height. In
   particular no `U`-number in Mahler's classification is exceptional.

**Mechanism.** Take an approximant `xi` and clear its denominator.
* **Determinant bound.** Restricting scalars along a well-conditioned basis of
  `O_F[a xi]` gives an integral matrix. The determinant conjecture bounds its
  spectral mass in `(0, eps)` by `O(log H) / log(1/eps)`, and a similarity lemma
  passes the bound to the conjugate `A(xi)`.
* **Perturbation.** A norm perturbation of size `|z_0 - xi|` moves at least
  `kappa(z_0)` of kernel into that small spectrum, since `A(xi)` has the generic
  kernel away from finitely many algebraic jumps.
* **Conclusion.** Comparing the two gives the exponent `C / kappa`.

**Consequences.**
* **At the master host.** If the master host `E` satisfies Strong Atiyah over
  `Qbar` and the determinant conjecture, then
  `algebraic-atiyah-and-determinant-one-group-tester` gives both for every
  torsion-free group, hence this conclusion for every torsion-free group.
* **Shape of a failure.** A failure of Strong Atiyah over `Qbar(z)` then needs a
  badly approximable transcendental `z`. That is a restriction in arithmetic, not
  in measure.
* **Where it stops.** The box principle of `serre-class-atoms-obey-degree-bound`
  would empty the exceptional set if the companion matrices over the skew field
  had fixed-size integral models under polynomials. Their linear representations
  grow linearly with the degree, and the gain cancels (artifact, Section 5).

**Model test.** Sofic groups satisfy both hypotheses and have empty exceptional
set, consistent with the conclusion. The hypotheses cannot be dropped to
tracial models. A skew field `Qbar(t)` with `t` carrying an atom at a Liouville
number `L` has `L` exceptional. Such a `t` has no integral model obeying a
determinant bound, which is exactly where the argument uses the group.
