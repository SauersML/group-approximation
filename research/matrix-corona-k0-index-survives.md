---
rg: 2
id: matrix-corona-k0-index-survives
kind: claim
title: K-zero of a matrix corona is the product modulo the sum
distinct_from:
  matrix-corona-k1-vanishes: that is the vanishing of K_1, which kills index invariants of a single marked unitary; this is the computation of K_0, which shows the pair invariants survive.
  exel-loring-relative-quasirep-invariant: that records the external construction of the relative invariant; this is the corona-side computation saying where such an invariant can live.
---

For any sequence `(d_n)` of positive integers,

    K_0( prod_n M_{d_n} / oplus_n M_{d_n} )  ==  prod_n Z / oplus_n Z.

Together with `matrix-corona-k1-vanishes` this delimits index arguments in
the non-MF program exactly.  A single marked unitary carries a `K_1` class
and `K_1` of the corona is zero, so nothing survives.  A commuting **pair**
in the corona is a homomorphism from `C(T^2)`, and the image of the Bott
generator lands in `K_0`, which is large: concretely, the sequence of Bott
indices of any lift, read modulo eventual agreement.  Different lifts of the
same corona pair differ by a sequence tending to zero in norm, and the Bott
index is stable under small perturbations, so the class is an invariant of
the corona representation and not of the chosen lift.

So relative index arguments are not formally dead, and the group has to
supply the second operator.  This is the corona-side half of the programme
recorded in `exel-loring-mark-quantization`.
