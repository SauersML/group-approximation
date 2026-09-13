---
rg: 2
id: algebraically-independent-points-approximable-by-zero-cycles
kind: claim
title: A point of C^s with algebraically independent coordinates admits integral Chow forms of zero-dimensional cycles whose values on hyperplanes through the point beat any fixed multiple of height plus degree
distinct_from:
  determinant-conjecture-bounds-determinants-over-galois-orbits: that is the operator inequality every such form must satisfy at an exceptional point; this is the purely Diophantine existence of forms violating it.
artifacts:
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part3.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part4.md
---

**OPEN for s >= 3. Proved for s = 2** (Part 3 of the artifact, unreviewed).

Let `s >= 3` and let `z in C^s` have algebraically independent coordinates. Put
`theta~ = (1, z) in C^(s+1)`.

For a form `F in Z[u_0..u_s]` that is a constant times a product of linear forms
`u . (1, zeta)` at points `zeta in Qbar^s`, define:
- `b(F) = log M(F)`, the Mahler measure;
- `a(F) = log M(v -> F(S_theta v))`, where `S_theta` is a fixed linear
  parametrization of the hyperplane `{u : u . theta~ = 0}` with integral-bounded
  entries. For `s = 2` this is the cross product.

**Claim.** For every `B >= 1` and `C >= 0` there is such an `F` with

```text
a(F) + (B - 1) b(F) + C deg F  <  0.
```

**Why it matters.** Together with the `s`-variable versions of Lemma J, (RES2),
Lemma H and Corollary 6 (Parts 1-2), it gives Strong Atiyah over
`Qbar(z_1..z_s)` under the determinant conjecture. The fibre argument of Part 4
then extends it to every field of transcendence degree `s`.

**Heuristic.** Counting cycles of degree `D` and height `h` against the volume
of neighbourhoods of `z` suggests a ratio `-a/b` of order `D/(2s)`. So such forms
should exist in every dimension.

## Attempts

* **s = 2: one irreducible bivariate `p_1` and one univariate `q`.** This
  works. The cycle `V(p_1, q)` is automatically zero-dimensional. The exponents
  `n^2/4` for `p_1` and `n_2/2` for `q` beat the losses `n_2` and `n` with
  `n ~ 100 B^2` and `n_2 ~ 4Bn`.
* **Triangular chains in three variables.** They die on degrees.
  - Take `f_i` from lattices of dimension `dim V_i` with exponent
    `w_i ~ dim V_i / 2` and degree `delta_i`. Branch `i` of the Sylvester
    recursion needs `w_i delta_i >~ B prod_j delta_j`.
  - For `q(x_1)`, `p_2(x_1,x_2)`, `p_3(x_1,x_2,x_3)`, in any order, this forces
    `n_3 >~ 2B n_1 n_2`, `n_2 >~ 8 B^2 n_1^2` and `n_1^2 >~ 24 B^2 n_2^2`, which
    are incompatible.
* **A two-variable cycle as base, with a trivariate top.** It dies on degrees.
  - The base branch loses `D' L_3`, where `D' ~ B'^5` is the degree of the
    `S(2)` construction at ratio `B' ~ 2Bn_3`.
  - The gain is only `n_3^3 L_3`.
* **Degree-constrained second polynomial.** Coprimality is automatic if
  `deg_(x_3) p_2 < deg_(x_3) p_1`, which gives exponent `~ d_1 n_2^2/4`. With a
  univariate third polynomial the branch conditions still fail by a factor of
  `B^6`.
* **Curve, then a univariate cut.** Intersecting a curve `Gamma` with `q(x_1)`
  needs `g_Gamma >~ 4B^2 deg(Gamma) h(Gamma)`. The curves `V(p_1, q(x_1,x_2))`
  only reach `g/h ~ deg^(5/7)`.
* **Nesterenko-Philippon elimination with all polynomials in `s` variables.**
  The exponents close, since `w ~ n^s/(2 s!)` against a loss of `n^(s-1)`, but
  transversality needs control of the successive minima. Not attempted.
  Philippon, *Approximations algebriques des points dans les espaces projectifs
  I*, J. Number Theory 81 (2000) 234-253, doi:10.1006/jnth.1999.2461, looks like
  the natural source. Its statement and its normalization of the algebraic
  distance have not been checked, because the source could not be retrieved in
  this session.
* **Literature (read from hal-00480924, pp. 2-3).**
  - The full claim follows from [[philippon-zero-cycle-approximation-conjecture]],
    through `zero-cycle-approximation-via-philippon-conjecture`.
  - Philippon says he proved it in dimension `<= 3` in JNT 81 (2000). If that
    covers the arithmetic zero-cycle statement for `n = 3`, transcendence degree 3
    follows. The theorem number and statement still have to be read from JNT 81.
  - He calls it open for `n > 3`, blocked only by an effective lower bound for
    arithmetic Hilbert functions.
* **Credit.** For `s = 2`, Part 3 is an elementary, self-contained proof of a
  weak special case of Philippon's 2000 theorem. The new content of the
  two-variable artifact is the operator side: (RES2), Proposition C,
  Corollary 6 and Lemma J, and its link to the Atiyah base change.
