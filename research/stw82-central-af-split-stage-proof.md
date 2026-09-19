---
rg: 2
id: stw82-central-af-split-stage-proof
kind: route
title: Approximate the central quotient by clopen steps and decompose each stage into unitized ideal corners
target: stw82-central-af-split-extensions-obey-maximum
requires: []
artifacts:
  - research/artifacts/stw82-central-af-split-extension-audit-2026-08-30.md
---

Write `D` as the directed closure of its unital finite-dimensional
subalgebras `D_lambda`.  Since `D` embeds in the abelian algebra `Z(E)`,
each `D_lambda` is `C^{m(lambda)}`.  Define

`E_lambda = I + s(D_lambda) subset E`.                          `(CSP1)`

This is a C*-subalgebra: `I` is an ideal, `s(D_lambda)` is
finite-dimensional, and the sum is closed.  If
`e_1,...,e_m` are the minimal projections of `D_lambda`, then
`p_j=s(e_j)` are central orthogonal projections summing to `1_E`.  Hence

`E_lambda = direct_sum_{j=1}^m p_j E_lambda`,
`p_j E_lambda = p_j I + C p_j = unitization(p_j I)`.             `(CSP2)`

The last identification is injective because `q(p_j)=e_j` is nonzero.
Nuclear dimension is unchanged by minimal unitization and obeys the maximum
formula on finite direct sums.  Since

`I = direct_sum_{j=1}^m p_j I`,                                 `(CSP3)`

we obtain

`dim_nuc(E_lambda)
 = max_j dim_nuc(unitization(p_j I))
 = max_j dim_nuc(p_j I)
 = dim_nuc(I)`.                                                  `(CSP4)`

Finally, every `x in E` has the exact form
`x=(x-s(q(x)))+s(q(x)) in I+s(D)`.  Approximating the second term by
`s(D_lambda)` shows that the directed union of the `E_lambda` is dense in
`E`.  The local/inductive-limit permanence of nuclear dimension gives
`dim_nuc(E) <= dim_nuc(I)`.  The reverse inequality follows because
nuclear dimension does not increase from an algebra to an ideal.  Since
`dim_nuc(D)=0`, this proves `(CAS2)`.

The proof also identifies why centrality matters.  Without it the minimal
projections of a finite-dimensional split quotient need not give central
corners of `E_lambda`; the direct-sum decomposition `(CSP2)`, which is what
reuses the ideal colours, disappears.
