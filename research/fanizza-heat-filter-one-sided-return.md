---
rg: 2
id: fanizza-heat-filter-one-sided-return
kind: claim
title: Return the Fanizza heat-filter sequence to one fixed carrier only in finite matrices
distinct_from:
  affine-leavitt-steinberg-hs-coefficient-decoder: that decodes a full relative Leavitt coefficient cell; this only has to return the explicit rational contraction `K_m=1-H_m`.
  single-triangle-trace-cyclic-return-cell: that targeted a native incidence chord which disappears after the Pauli reduction; this has no context holonomy and uses the game Hamiltonian directly.
---

OPEN.  Starting from the finite presentation of the two-copy native variable
group and the finite rational group-algebra contraction

```text
K_m=1-H_m,
```

construct a finite ordinary-group extension with a fixed group-algebra mark
`p_m` such that:

1. the perfect HALT representation, after countable amplification, extends
   and keeps `p_m` nonzero;
2. every finite-dimensional microstate with vanishing relator defect decodes,
   for arbitrarily large virtual depth `t`, a returned copy of `p_m` whose
   norm is bounded by a fixed loss plus `||D_R K_m^t||`;
3. the loss is independent of matrix dimension and tends to zero at fixed
   `t` with relator defect; and
4. the return is not a universal tracial equality and therefore does not
   contradict the regular representation.

By `fanizza-heat-filter-has-uniform-cstar-decay`, the nonmember bound is

```text
||D_R K_m^t|| <= sqrt(C_m/(2t+1)).                    (FHR1)
```

Taking the microstate limit first and `t->infinity` second collapses the
fixed mark.  Exact HALT completeness uses only the ground-space identity
`K_m xi=xi` on one properly infinite representation.

The firewall is essential.  A literal group conjugacy between `p_m` and
`D_R K_m^t` would preserve norm in every representation and make the HALT
model impossible.  The return must appear only after a finite-dimensional
packet/multiplicity compression, exactly where cyclic trace or finite rank is
available.
