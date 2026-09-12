---
rg: 2
id: generic-cp-noise-maximizes-range-block-degree
kind: claim
title: Arbitrarily small cp noise can make every positive lift range-irreducible
distinct_from:
  vanishing-corner-reduction-maps-defeat-tracial-cp-upgrade: that hides non-cp behavior on a negligible corner; this makes the generated range algebra a full matrix factor on all coordinate mass while changing the quotient class by zero.
  maslov-diverging-positive-lifts-have-vanishing-high-degree-mass: that asks for a specially chosen low-degree lift; this proves that the degree distribution is maximally noncanonical and cannot be forced for every lift by quotient-level arithmetic relations.
---

Let `S` be a finite-dimensional operator system whose self-adjoint quotient
`S_sa/R1` has real dimension at least two.  For every `d>=2`:

1. there is a ucp map `Psi:S->M_d` with `C^*(Psi(S))=M_d`;
2. if `phi:S->M_d` is unital and `k`-positive, then for arbitrarily small
   `t>0` the unital `k`-positive map

   ```text
   phi_t=(1-t)phi+t Psi
   ```

   also satisfies `C^*(phi_t(S))=M_d` and

   ```text
   ||phi_t(x)-phi(x)|| <= 2t ||x||.                       (GCP1)
   ```

Consequently any sequence of finite-order positive lifts of a fixed
tracial-ultraproduct map can be replaced, without changing that map, by
lifts whose generated range algebra is `M_(d_n)` at every coordinate.  On
coordinates where `k_n<d_n`, their supercritical mass is exactly one.

This does not refute the existential `(MH1)`, because a different carefully
selected lift might have low-degree range.  It does prove a sharp no-go:
the Kassel word defects, central-regular scalar moments, and every other
quotient-level relation are unchanged by an `o(1)` perturbation, yet the
range-degree statistic jumps to its maximum.  Therefore those data cannot
prove `(MH1)` for arbitrary positive lifts, and no blockwise argument may
treat the decomposition of `C^*(phi_n(S))` as canonical.

The same perturbation also fences the two most direct proposed arithmetic
attacks.  No fixed nonzero polynomial identity can hold on all coordinate
range algebras: after perturbation the range is `M_d`, whose PI degree tends
to infinity with `d` (in particular the Amitsur--Levitzki identities have
unbounded degree).  Likewise, centralizer and finite-representation degree
bounds for exact Kassel representations do not apply to these ranges: the
range is already irreducible, although the map from `S` is not
multiplicative.  Either attack first needs a dimension-independent theorem
correcting the positive lift to an exact representation, which is precisely
the missing stability input.
