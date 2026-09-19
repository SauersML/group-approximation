---
rg: 2
id: free-compressor-tree-first-hit-and-rank-audit
kind: route
title: Partition the free compressor tree, move each leaf inside its parent stabilizer, and audit adjoint rank
target: free-compressor-tree-has-constant-first-hit-mover-mass
requires:
  - opposite-transvections-are-free-but-finite-lamp-windows-close
  - property-t-hs-positive-density-commutant-no-growth
  - infranormal-compact-closure-normal
  - aggregate-leaf-bessel-fails-after-prefix-transport
---

Use one Bernoulli lamp bit at every internal positive word to form the dyadic
cylinders `(FCT2)`.  The first differing branch bit proves orthogonality and
recursive summation proves that the cylinders partition one.  Nested
compressor subgroups make the leaf exit `H_w`-fixed.  A fixed element
`r_S in Gamma\S Gamma S^(-1)`, conjugated by the parent word, fixes the full
prefix and moves only the leaf site.  Canonical Bernoulli independence then
gives `(FCT3)--(FCT6)`.

Regard the exits as vectors in normalized `L^2(M_d)`.  Counting their span
gives `(FCT7)`, which is below the positive-density hypothesis of the
property-`(T)` no-growth theorem at every fixed depth.  Finally inspect the
finite congruence models: normality of the image of `Gamma` identifies the
two leaf sites, proving that precisely the stabilizer-moved correlation, and
not the positive prefix table, is absent there.

The aggregate audit uses `(ALB1)--(ALB4)`: orthogonality pays one fixed error
once, but prefix-dependent conjugation destroys it unless the transported
leaf family has a uniform frame bound. The canonical one-compressor lamp
then gives the exact property-`(T)` firewall, while the left-multiplier
calculation shows that superoperator amplification preserves the same gap.
