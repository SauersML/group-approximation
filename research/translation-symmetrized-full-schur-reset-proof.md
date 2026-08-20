---
rg: 2
id: translation-symmetrized-full-schur-reset-proof
kind: route
title: Extend every shifted child pencil by the constant Schur border row
target: translation-symmetrized-full-schur-reset
requires:
  - translation-symmetrized-schur-child-reset
  - predicate-rank-gate-doubles-restriction-multiplicity
  - shared-overlap-controls-packet-multiplicity-vector
---

For each translated copy, adjoin an involution `p_*^(a)` commuting with all
`p` generators and with generators in other copies, and impose

```text
[p_*^(a),q_j^(a)]=J^((e_s)_j),
[p_*^(a),q_*^(a)]=1.
```

These are exactly the bottom row of `(TFS1)`. They contain no selector
coefficient, so `tau_b` carries them to the identical relations in copy
`a+b`. Twisting `q_*^(a)` by the central involution `J` changes none of its
commutators, including the last displayed relation. The same is true when
twisting `p_*^(a)` by `J`, so the independent `P` flips in `(TFS3)` are also
automorphisms. Hence all automorphisms extend and `(TFS4)` is finite.

In a `J=-1` representation, the selector translations make all selector
spaces `H_x` equidimensional. On an active sector, the full packet algebra is
`M_(2D)(C)` and has one simple. On an inactive sector it is
`M_D(C) tensor C[(C_2)^2]`; the two branch flips act transitively on its four
simples. If `h=dim(H_x)`, the active multiplicity is `h/(2D)` and each
inactive multiplicity is `h/(4D)`. Since `f` is nonconstant, an inactive
sector shows that `h` is divisible by `4D`. Setting `n=h/(4D)` proves
`(TFS5)`.

For approximate tables, exactify `Rhat_f`. Its exact `B_f` vector lies on
the displayed ray. Polar alignment with any separately exactified occurrence
of the same `B_f` and `(OMV1)` bound the weighted transverse discrepancy by
the fixed correction loss. This gives the quantitative statement.
