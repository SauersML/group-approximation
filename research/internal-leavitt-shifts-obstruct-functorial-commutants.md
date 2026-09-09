---
rg: 2
id: internal-leavitt-shifts-obstruct-functorial-commutants
kind: claim
title: Every ambient embedding contains an internally shifted Leavitt copy with distance-one commutant excess
distinct_from:
  diagonal-leavitt-models-have-external-commutant-excess: That embeds a diagonal copy into an external tensor-square algebra; this uses a fixed injective native ring endomorphism inside the original group algebra and works in every extension of that original algebra.
  leavitt-root-fixed-projections-equal-the-global-fixed-projection: That determines left fixed projections and all character weights; the shifted copies retain the regular character but fail a functorial recovery of their conjugation commutants.
artifacts:
  - research/artifacts/leavitt-internal-shift-commutant-obstruction-2026-09-08.md
---

Let `H=R^x`, `R=L_(F_2)(1,2)`, and let `L,K` be the native
commuting `3+1` subgroups in `H~=GL_4(R)`. Fix any complete binary
prefix code `alpha_1,...,alpha_m` with `m>=2`, and define

```text
sigma_m(r)=sum_i s_(alpha_i) r t_(alpha_i).
```

This is an injective unital ring endomorphism, corresponding to
`r -> diag(r,...,r)` under `R~=M_m(R)`. For `N=L(H)`, write
`N_m=L(sigma_m(H))`, `A_m=L(sigma_m(L))`, and
`B_m=L(sigma_m(K))`, all inside `N`.

For every finite tracial extension `Q` of `N`, set

```text
D_Q=B_m join (N_m' intersect Q).
```

The group centralizer of `sigma_m(H)` is the native scalar
matrix group `F_m=GL_m(F_2)`, and

```text
D_Q intersect N = L(sigma_m(K) F_m).
```

For every `k in K\{1}`, the group unitary associated with
`diag(k,1,...,1)` belongs to `A_m' intersect Q`, but its
conditional expectation onto `D_Q` is zero. Its distance from
`D_Q` is exactly one in normalized HS norm.

Consequently no embedding of `N` can recover these native relative
commutants functorially under the fixed internal substitutions
`sigma_m`, even after adjoining the whole shifted group's ambient
commutant. This does not exclude a specially chosen embedding with
the desired property for the original, unshifted subgroups. No
inner or approximately inner implementation of the shift, and no
nonhyperlinearity conclusion, is assumed or proved.
