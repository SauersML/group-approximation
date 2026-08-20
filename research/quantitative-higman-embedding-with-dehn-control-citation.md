---
rg: 2
id: quantitative-higman-embedding-with-dehn-control-citation
kind: route
title: Import Chornomaz-Wagner's refinement of Birget-Olshanskii-Rips-Sapir
target: quantitative-higman-embedding-with-dehn-control
requires: []
---

Literature import.  `arXiv:2304.07603v1`, environment labelled
`th-BORS-1-1-improved`, transcribed verbatim, together with the definition of
the relative Dehn function given immediately after it in the source and the
quasi-optimality discussion of the following paragraph.

Their proof is three lines given the machine: the group is `H_N(S_eps)` built
exactly as `H_N(S)` in BORS Section 6, whose Dehn bound
`O(n^6) + O(T(O(n^2))^4) + O(n^2 T(O(n^2))^4)` has its second and third terms
supplied by the *area* complexity of the emulating machine, so substituting
`S_eps` replaces the exponent `4` by `2+eps` throughout.  The "moreover" clause
about the Dehn function of `G` in `H` is, as the source notes, not formulated
in BORS but immediate from their construction, where it would read `T(n)^4`.
