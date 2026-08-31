---
rg: 2
id: polynomial-qutrit-chart-has-hyperlinear-steinberg-lift
kind: claim
title: The polynomial qutrit chart remains hyperlinear in the Steinberg cover
artifacts:
  - research/polynomial-qutrit-steinberg-lift-proof.md
distinct_from:
  depth-mismatched-qutrit-root-bridge-is-residually-finite: that embeds the literal downstairs subgroup in GL_28(F_2[T]) and leaves its restricted central extension open; this constructs a split polynomial lift and compares it with the chosen Thompson and standard-root lifts.
  thompson-v-lifts-through-binary-leavitt-steinberg-cover: that uniquely splits the cover over the Thompson subgroup alone; this simultaneously includes the incompatible-depth opposite roots.
  positive-steinberg-qutrit-bridges-are-central-by-finite: that gets amenability from a finite positive-root image; this treats an infinite, nontriangular, residually finite polynomial image.
---

Let `R=L_(F_2)(1,2)`, let `F` be the transitive qutrit packet on
`D_27`, and for `n>=5` let

```text
Gamma=<iota_n(F),x_12(s_0),x_21(t_00)> <= St_n(R),       (PQS1)
```

where `iota_n` is the unique Thompson lift and the other two generators
are the standard Steinberg roots.  Then `Gamma` is hyperlinear.

More precisely, the polynomial chart from the depth-mismatch theorem has a
homomorphic section

```text
s:H -> St_n(R),                 pi_n o s=id_H,           (PQS2)
```

where

```text
H=<D_n(F),e_12(s_0),e_21(t_00)>
  <= GL_28(F_2[T]).
```

There is a finite central subgroup `C` of `St_n(R)` such that

```text
Gamma <= C s(H).                                         (PQS3)
```

Since `H` is residually finite and `C s(H)` is a finite extension of
`H`, both `C s(H)` and its subgroup `Gamma` are hyperlinear.

Thus neither the first incompatible Leavitt depth return nor the restricted
Steinberg kernel supplies a nonhyperlinear group.  The next root package must
leave every one-variable polynomial chart—for example by producing both
one-sided coefficients `S,T` with `TS=1), or two return parameters which
cannot be placed in one residually finite coefficient algebra.
