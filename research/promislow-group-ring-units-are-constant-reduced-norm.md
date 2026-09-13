---
rg: 2
id: promislow-group-ring-units-are-constant-reduced-norm
kind: claim
title: An element of R[P] is a unit exactly when its explicit invariant quartic reduced norm is a unit of R
distinct_from:
  rational-unit-conjecture-torsion-free: that asserts trivial units over Q for every torsion-free group; this is an exact unit criterion on one group that proves no triviality.
  support-pair-unit-scheme-is-finite-over-z: that bounds the units on one fixed support pair; this decides whether any single element is a unit, with no support or inverse data.
  promislow-radius4-one-sided-and-integral-separation: that is a radius-four census over F_2 with an integral lifting obstruction; this is a unit criterion over every commutative domain.
artifacts:
  - research/artifacts/promislow-reduced-norm-2026-09-13.md
---

**ESTABLISHED.** Let `P = <a, b | b^-1 a^2 b = a^-2, a^-1 b^2 a = b^-2>` be the
Promislow group, with `x = a^2`, `y = b^2` and `z = (ab)^2`. These generate a
free abelian normal subgroup `L` of index 4, and `P/L` is the Klein four-group
`K4`. Conjugation by the coset representatives acts on `R[L]` as follows:

| conjugation by | action on `(x, y, z)`       | notation   |
|----------------|-----------------------------|------------|
| `a`            | `(x, y^-1, z^-1)`           | `f -> f^A` |
| `b`            | `(x^-1, y, z^-1)`           | `f -> f^B` |
| `ab`           | `(x^-1, y^-1, z)`           | `f -> f^C` |

Let `R` be a commutative domain. Every `u in R[P]` is uniquely
`u = p + q a + r b + s ab` with `p, q, r, s in R[L]` (coefficients on the left).
Define `Nrd(u)` as the determinant of right multiplication `w -> w u`, viewed
as a left `R[L]`-linear map of the free module `R[P]` with basis `(1, a, b, ab)`.

1. **Formula.** `Nrd(u)` is the sum of the following 24 terms, copied
   verbatim from the script output (log line `G1`):

       + p^A p^B p^C p            - p^A p^B s^C s z          - p^A p^C r^B r y
       - p^A p q^B q^C x^-1       + p^A q^B r s^C x^-1 y     + p^A q^C r^B s z
       - p^B p^C q^A q x          - p^B p r^A r^C y^-1       + p^B q^A r^C s x y^-1
       + p^B q r^A s^C z          - p^C p s^A s^B z^-1       + p^C q^A r s^B z^-1
       + p^C q r^B s^A x y        + p q^B r^C s^A z^-1       + p q^C r^A s^B x^-1 y^-1
       + q^A q^B q^C q            - q^A q^B r^C r z^-1       - q^A q^C s^B s y^-1
       - q^B q s^A s^C y          - q^C q r^A r^B z          + r^A r^B r^C r
       - r^A r s^B s^C x^-1       - r^B r^C s^A s x          + s^A s^B s^C s

   Only this verbatim list is authoritative. The four displayed lines above it
   are an informal regrouping.
2. **Invariance and multiplicativity.** `Nrd(u)` is `K4`-invariant, and
   `Nrd(uv) = Nrd(u) Nrd(v)`. Also `Nrd(lambda g) = lambda^4` for
   `lambda in R` and `g in P`.
3. **Criterion.** `u` is a unit of `R[P]` if and only if `Nrd(u) in R^x`.
   In that case

       u^-1 = -Nrd(u)^-1 (u^3 - c_1 u^2 + c_2 u - c_3),

   where `T^4 - c_1 T^3 + c_2 T^2 - c_3 T + Nrd(u)` is the characteristic
   polynomial of the matrix of `w -> w u`. Its coefficients `c_i` are
   `K4`-invariant, hence central in `R[P]`.

**Credit.** The criterion is not new. Tabei (arXiv:2608.00103, TeX
Section 2, "The determinant criterion") attributes it to Craven--Pappas,
J. Algebra 394 (2013): Thm. 6.8, specialized to the fours group as their
"Determinant condition" (Thm. 8.5), with the embedding at Thm. 8.6. Tabei
attributes the embedding for this group to Passman (2021). Those primary
sources were not read here. The proof in the route is self-contained, and the
explicit formula is computed exactly by
`research/artifacts/promislow-reduced-norm-cp.py`. No novelty is claimed.

**Scope.** This decides whether a single element is a unit. It says nothing
about whether nontrivial units exist over `Q` or `Z`.

DERIVATION
[[promislow-reduced-norm-criterion-proof]]
