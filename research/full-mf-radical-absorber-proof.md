---
rg: 2
id: full-mf-radical-absorber-proof
kind: route
title: Restrict every MF representation to the absorber and then divide by its normal closure
target: full-mf-radical-absorber
requires:
  - universal-mf-quotient
artifacts:
  - research/full-mf-radical-absorber.md
---

Let `f : G -> M` be a homomorphism to a countable MF group.  The composite

```text
A --j--> G --f--> M
```

is trivial because `Rad_MF(A)=A`.  Hence `f` kills `j(A)`, and normality of
its kernel gives `N <= ker(f)`.  Every MF representation of `G` therefore
factors uniquely through `pi : G -> G/N`.

This factorization gives both containments in `(A1)`.

* If `g` belongs to `pi^(-1)(Rad_MF(G/N))`, every MF representation of `G`
  descends to an MF representation of `G/N` and kills `pi(g)`, so it kills
  `g`.
* If `g` does not belong to that preimage, the definition of
  `Rad_MF(G/N)` supplies a homomorphism from `G/N` to an MF group which does
  not kill `pi(g)`.  Its composite with `pi` detects `g`.

Thus `Rad_MF(G)=pi^(-1)(Rad_MF(G/N))`.  The third isomorphism theorem gives
`(A2)`.

For `G=A x B`, quotienting by the first factor gives `B`, and the preimage of
`Rad_MF(B)` is `A x Rad_MF(B)`.  For `G=A * B`, quotienting by the normal
closure of the first free factor gives `B`, so the same formula identifies
the universal visible quotient with `B/Rad_MF(B)`.  The extension statement
is the identical argument with its given normal kernel.

