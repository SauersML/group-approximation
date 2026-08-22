---
rg: 2
id: finite-packet-codensity-folds-forty-two-atom-proof
kind: route
title: Combine the rational finite-subgroup bound with arithmetic co-density
target: sl3-one-over-forty-two-packet-is-external-or-folded
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
  - sl3-raw-weyl-rectangle-pins-only-equal-rank-corners
  - balanced-raw-lamp-orbit-cannot-approximate-shell-pvm
---

# Combine the rational finite-subgroup bound with arithmetic co-density

The finite-rotation-group classification and the cyclotomic-degree argument
give `|K|<=24` for finite `K<SL_3(Q)`.  A projection in the finite group
algebra has integer rank in the regular representation, proving `(OFP2)` and
the internal obstruction.

For an external exact packet, the established arithmetic co-density theorem
gives `(OFP4)`.  A base atom of an `A/C` system is `C`-fixed by definition,
so it is `A`-fixed and its orbit is a singleton.  Applied to `(OFP6)`, all
refined branches remain under one trace-`1/21` support, which cannot contain
42 orthogonal projections of trace `1/42`.

Finally, dropping `C`-fixedness removes the hypothesis which makes the
section words independent of their right corrections `d_i`.  This is exactly
the commutator term in the established raw-incidence estimate, proving the
stated dichotomy.
