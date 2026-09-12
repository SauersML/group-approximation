---
rg: 2
id: rstar-sunflower-full-link-proof
kind: route
title: Assemble independent petal extensions around the fixed center atom
target: rstar-sunflower-neighborhoods-have-full-links
requires:
  - rstar-fano-ghost-affine-hull-criterion
---

For each petal block choose the extension required in hypothesis 3.  On an
intersection with the center it equals the already fixed assignment `a`.
Outside the center, two different blocks have disjoint variable sets.
Their union is therefore a well-defined assignment satisfying every block,
which is an element of `Link(c,a)`.

For the `R_*` specialization, fixing at most two coordinates leaves at
least two odd-parity completions before the ghost is deleted.  Deleting one
point leaves at least one completion.  This verifies hypothesis 3 for each
single-constraint petal and proves the claim.

