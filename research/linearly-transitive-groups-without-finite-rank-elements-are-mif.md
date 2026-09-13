---
rg: 2
id: linearly-transitive-groups-without-finite-rank-elements-are-mif
kind: claim
title: Linear groups over a finite field that extend every finite-dimensional partial isomorphism and have no finite-rank scalar perturbations are MIF
distinct_from:
  fp-simple-highly-transitive-groups-satisfy-pbh: that is BFFHZ Theorem C, which takes MIF as a hypothesis; this is a sufficient condition for MIF itself, for groups acting linearly rather than on sets.
  binary-leavitt-unit-group-is-mif: that applies the criterion to Leavitt unit groups through the Cantor module; this is the abstract criterion.
---

**ESTABLISHED** through `linearly-transitive-groups-without-finite-rank-mif-proof`,
a direct proof. Not independently reviewed; no novelty is claimed.

Let `F` be a finite field, `M` an infinite-dimensional `F`-vector space and
`G <= GL(M)`. Assume:

- **(E) linear high transitivity.** For all finite-dimensional subspaces `A, B <= M`
  and every linear isomorphism `φ : A -> B` there is `g ∈ G` with `g|_A = φ`.
- **(R) no finite-rank scalar perturbations.** For every `g ∈ G` and `λ ∈ F` with
  `g != λ·id_M`, the image `(g - λ)M` is infinite-dimensional.
- **(Z) no nontrivial scalars.** The only scalar operator in `G` is `id_M`. Over
  `F_2` this is automatic.

Then `G` is mixed-identity-free. That is, for every `w ∈ G * <x>` with `w != 1` there
is `g ∈ G` with `w(g) != 1`, where `w(g)` is the image of `w` under the homomorphism
`G * <x> -> G` that is the identity on `G` and sends `x` to `g`.

## Neither hypothesis can be dropped

- **(R) is needed.** Over `F_2`, the finitary group of all `g` with `(g - 1)M`
  finite-dimensional satisfies (E), but it is not MIF.
  - Let `t = 1 + e` with `e` of rank one and `e^2 = 0`. For any `x`, the group
    `H = <t, x t x^-1>` fixes `K = ker e ∩ ker(x e x^-1)` pointwise, and every
    `h ∈ H` has `(h - 1)M ⊆ W = im e + im(x e x^-1)`.
  - Such `h` is determined by the induced linear map `M/K -> W`, both of dimension
    at most 2, so `|H| <= 16`.
  - Hence `(t x t x^-1)^N = 1` for `N = lcm(1, ..., 16)`, a nontrivial element of
    `G * <x>`.
- **(Z) is needed.** A central scalar `λ != 1` in `G` gives the mixed identity
  `λ x λ^-1 x^-1`. For example, `L_(F_3)(1,2)^×` satisfies (E) and (R) on its Cantor
  module, by the argument of `binary-leavitt-unit-group-mif-proof`, but contains `-1`.

## Use

`binary-leavitt-unit-group-is-mif` applies this to the unit group of
`L_(F_2)(1,n)`, acting on its Cantor module. This is the finitely presented simple
group left undecided by Attempt 4 on `fp-simple-groups-embed-in-fp-simple-mif-groups`.
