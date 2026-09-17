---
rg: 2
id: fpbs-morse-mass-bounded-by-relator-boundary-rank
kind: claim
title: The mass of a well-founded Borel Morse matching is at most the von Neumann rank of the relator boundary, so the Morse deficit splits into a relation gap and an attainment defect
artifacts:
  - research/artifacts/fpbs/docs/morse-l2-inequality-and-lamplighter-gap.md
distinct_from:
  fpbs-bernoulli-morse-collapse-criterion: that bounds the Bernoulli cost by the matched mass and caps the mass by the full cycle dimension z; this caps the mass for a fixed finite list by the smaller rank of that list's boundary operator, which can stay below z for every finite list
  fpbs-morse-deficit-vanishes-for-full-presentations: that is the open assertion that the deficit over growing lists tends to zero; this proves a lower bound for each fixed list and shows the limit statement is equivalent to vanishing of the attainment defect
  fpbs-graphing-cost-betti-cycle-dimension-identity: that is the dimension identity for a graphing; this is a dimension inequality for cell matchings, proved by dense range of the matched-edge projection of the relator boundary
  first-l2-betti-at-least-negative-orbifold-char: that bounds the rank of a relator boundary above by the orbifold count of cell orbits; this bounds Borel matched mass above by that rank
---

**PROPOSED ESTABLISHED.** A written deduction over established nodes; see the route
`fpbs-morse-mass-bounded-by-relator-boundary-rank-proof`.

**Setting.** As in `fpbs-bernoulli-morse-collapse-criterion`: `Gamma` infinite with finite generating set `S`, a free
p.m.p. action (for instance Bernoulli) with Cayley graphing `Phi_S`, a finite list `R` of trivial words, and Morse
matchings `M` of the `R`-cells satisfying (M1)–(M3). Let `d2^R` be the boundary operator from the cell module
(dimension `|R|`) to the edge module of `Phi_S`, and `rho(R) = dim_R cl im d2^R`.

**Theorem C.** Every Morse matching satisfies `mu(M) <= rho(R)`. Equivalently the unmatched cells have density at
least `dim_R ker d2^R`.

**Decomposition.** With `gap(R) = z(Phi_S) - rho(R)` and `A(R) = rho(R) - sup_M mu(M)`, both nonnegative,

```text
m(R) = gap(R) + A(R),     gap(P_L) = tau_L(Phi_S) -> 0,     lim_L m(P_L) = lim_L A(P_L).
```

So `fpbs-morse-deficit-vanishes-for-full-presentations` is equivalent to asymptotic attainment of the l2 bound,
`lim_L A(P_L) = 0`. For a finite presentation `gap = 0`, and deficit zero means `A(R) = 0`.

**Consequences recorded in the artifact.** Theorem C recovers Proposition C of the collapse note (the proper-power
ceiling `1/m`) and extends its unmatched-density Remark from finite presentations to every finite list.

**Proof idea.** Project `d2^R` onto the removed-edge module `C_1(E_M)`, of dimension `mu(M)`. A vector on `E_M`
orthogonal to the range is killed by the adjoint boundary. Since each matched edge occurs once on its cell (M1), its
value is a signed sum of the values on its children, and induction on the finite recovery-tree height (M3) gives zero.
So the projection has dense range, and `mu(M) <= dim cl im d2^R`.

## Attempts

(none)
