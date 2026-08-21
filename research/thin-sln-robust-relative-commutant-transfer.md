---
rg: 2
id: thin-sln-robust-relative-commutant-transfer
kind: claim
title: Almost centralizing a thin profinitely dense subgroup in an approximate SL_n(Z) representation forces almost centralizing the lattice
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  sln-z-flexibly-hs-stable: that corrects the entire approximate lattice representation to an exact representation after flexible padding; this asks only for one auxiliary unitary and one commutator, with no tuple correction.
  hnn-route-is-relative-commutant-collapse: that states the general ultraproduct wall; this is its explicit finite-stage form for a thin profinitely dense subgroup of the plain lattice SL_n(Z).
  canonical-trace-does-not-weaken-thin-commutant-transfer: that proves canonical trace tests do not make this claim easier; this is the open transfer assertion itself.
---

Use either the four-generated pair of `sln-z-thin-codense-tau-pair`, or the
preferred literal specialization

```text
A = SL_3(Z),  C = <c_1,c_2> = <a,b>,  c = r notin C,
```

from `explicit-sl3-thin-codense-tau-pair`.  Fix a finite presentation
`A = <S | R>` and words for the subgroup generators and outsider in `S`.

**Open transfer modulus.**  For every `epsilon > 0` there is `delta > 0`
such that, for every dimension `d`, every unitary tuple `U in U(d)^S`, and
every `v in U(d)`,

```text
max_(r in R) ||r(U)-1||_2 < delta,
max_i ||[v,c_i(U)]-1||_2 < delta
```

imply

```text
||[v,c(U)]-1||_2 < epsilon.                              (TRC1)
```

Equivalently, if `U_k` is any asymptotic matrix representation of `A`,
then in the tracial matrix ultraproduct

```text
U(C)' intersect M_omega = U(A)' intersect M_omega.       (TRC2)
```

It is enough to prove `(TRC1)` only for tuples whose traces converge to the
canonical trace of `A`: `canonical-trace-does-not-weaken-thin-commutant-transfer`
proves the converse by residual-finite tensor camouflage.

## Why this is the sharp HNN target

`non-hyperlinear-from-thin-sln-commutant-transfer` shows that `(TRC1)` makes

```text
<SL_3(Z), t | [t,a]=1, [t,b]=1>
```

non-hyperlinear, with marked word `[t,r]`.  Thus full flexible HS-stability
of `SL_n(Z)` is sufficient but unnecessarily strong: only the fate of the
single HNN implementer must be controlled.

Detinko--Flannery--Hulpke supply the literal matrices in rank three, so the
conditional HNN group is now fully explicit.  Aka--Gelander--Soifer remains
useful for the uniform all-ranks version.

## Exact endpoint already available

For every exact finite-dimensional representation `rho` of `A`, co-density
gives `rho(C)' = rho(A)'`.  Bourgain--Varju expansion gives a uniform
conjugation gap on precisely these representations, hence a constant `K`
independent of `rho` and its dimension such that

```text
dist_2(v,rho(A)')
 <= K max_i ||[v,rho(c_i)]-1||_2.                       (TRC3)
```

Therefore `(TRC1)` is exactly the robustification of a proved uniform
finite-dimensional inequality from exact representations to approximate
presentations.  It is not another finite-quotient expansion problem.

## Infinite-representation firewall

No inequality like `(TRC3)` can hold in all unitary representations.  In
the quasi-regular representation of `A` on `l^2(A/C)`, the projection onto
the base-coset vector commutes with `C` but not with `A`; its associated
selfadjoint unitary does the same.  Thus any proof of `(TRC1)` must use the
matrix/asymptotic-presentation coordinates.  Property `(T)`, property
`(tau)`, or a group-C-star-algebra sum-of-squares certificate valid in every
representation cannot by itself close the claim.

**Status: OPEN.**  This is strictly more mark-specific than flexible
stability, but by the tensor-camouflage theorem it is not weakened by
canonical trace side conditions.
