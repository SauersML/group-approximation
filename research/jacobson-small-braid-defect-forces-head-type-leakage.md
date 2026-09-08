---
rg: 2
id: jacobson-small-braid-defect-forces-head-type-leakage
kind: claim
title: A small Jacobson first-braid defect forces quantified mixing out of the two three-dimensional head types
artifacts:
  - research/artifacts/jacobson-all-head-braid-multiplicity-and-leakage-2026-09-08.md
distinct_from:
  del2-three-dimensional-head-braid-gap: that proves a uniform gap when the head has only the two three-dimensional irreducibles and trivial spectators; this allows all head types and quantitatively lower-bounds the matrix block by which the overlap-central involution leaves the three-dimensional head summands.
  jacobson-tail-braid-exactification-and-standard-carrier: that fixes the packet while imposing the second braid exactly and bounds its standard S3 carrier; this controls first-braid leakage out of specified head-isotypic subspaces, without assuming the second braid is exact.
  jacobson-two-braid-mixed-packet-gap: that asks for a positive all-dimensions infimum; this proves only a necessary leakage and dimension condition, compatible with large regular profiles.
---

Let `pi` be an arbitrary finite-dimensional exact representation of
`GL_3(F_2)_Q x GL_3(F_2)_P`, let `H` be a self-adjoint unitary
commuting with `K=GL(<e_1,e_3>)_Q`, and put

```text
B=pi(w_23,w_23),                  delta=||(HB)^3-I||_op.
```

Let `P` be the sum of the head-isotypic projections for the irreducibles
`3` and `3bar`, and set `m=rank(P)>0`, `E=(I-P)HP`. For the
unnormalized Hilbert--Schmidt norm,

```text
sqrt(m/30) <= delta sqrt(m)+3sqrt(2)||E||_F.               (HTL1)
```

In particular, an exact first braid requires

```text
||E||_F^2 >= m/540.                                      (HTL2)
```

Write `N_alpha` for the multiplicity of the head irreducible `alpha`
after forgetting the tail action. The `K`-commutant condition confines
the range of `E` to a space of dimension at most
`4N_6+6N_7+7N_8`. Therefore, when `delta<1/sqrt(30)`,

```text
4N_6+6N_7+7N_8
 >= (N_3+N_3bar)/6 * (1/sqrt(30)-delta)^2.                (HTL3)
```

For an exact braid, the right side is `(N_3+N_3bar)/180`.
No invariance of `P` under `H` is assumed. Arbitrary mixtures of all
head types, arbitrary tail actions, and arbitrary multiplicities are
allowed. The theorem does not establish positivity of the universal
two-braid infimum; profiles with adequate nontrivial head capacity remain.
