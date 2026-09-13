---
rg: 2
id: finite-moment-hardness-from-smooth-design
kind: route
title: Pointwise smooth pairing hardness supplies every fixed finite density moment
target: finite-moment-pairing-2to1-hardness
requires: [smooth-design-rich-2to1-hardness]
---

For the requested `m,K,q`, take the pointwise constant `B=C(K,m)` from
smooth-design hardness. On uniform probability space,
`1_E D<=B` implies `||1_E D||_q<=B`. Set the new constant to `B`,
independent of `eta,t,n`, and use the same hard regular instances at
arbitrarily large alphabets. Exact design moments and encoding are unchanged.

Together with the finite-moment route to UGC and the existing UGC-to-smooth
design padding route this produces a conditional equivalence cycle. It
establishes none of the open hardness claims by itself.
