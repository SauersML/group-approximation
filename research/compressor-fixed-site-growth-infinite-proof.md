---
rg: 2
id: compressor-fixed-site-growth-infinite-proof
kind: route
title: Turn one matrix entry negative along a transvection family
target: compressor-fixed-site-growth-infinite
requires: []
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

Conjugating `Gamma` by `(1,nu)` gives `EL_r(nu(R_+))`, which lies in
`EL_r(R_+)` exactly when `nu(R_+)<=R_+`, because entries of elementary
matrices realize every ring element; and since `nu` permutes monomials by
`x^v |-> x^(nu v)`, that is nonnegativity of `nu`.  This is the only input.

For `s=u_13` take `m_n=I+n e_12`, nonnegative with determinant one, so
`(1,m_n) in P_Gamma` and `(1,m_n^(-1))Gamma` is a `Gamma`-fixed site.  Its
image under `s` has inverse `(1,m_n u_13^(-1))`, and `m_n u_13^(-1)` differs
from `m_n` by a matrix whose third column is the first column of `m_n`,
namely `e_1`; the `(1,3)` entry therefore becomes `-1`, so the image is not a
fixed site.  Distinct `n` give distinct `SL_d(Z)`-components and `Gamma` has
trivial `SL_d(Z)`-component, so the cosets are pairwise distinct.  For
`s=u_32` the same computation with `m_n=I+n e_13` turns the `(3,2)` entry
negative.  Complete argument in the cited note, Proposition 7a.
