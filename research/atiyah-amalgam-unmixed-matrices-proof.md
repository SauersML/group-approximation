---
rg: 2
id: atiyah-amalgam-unmixed-matrices-proof
kind: route
title: Induction is dimension-preserving, so a subgroup-supported matrix keeps its von Neumann rank
target: atiyah-amalgam-unmixed-matrices-reduce-to-factors
requires: []
---

Let `H <= G` and pick left coset representatives `G = ⊔_i g_i H`. Then

```text
l^2(G) = ⊕_i g_i l^2(H),
```

and right multiplication `r_M` by `M in M_(m,n)(K[H])` preserves each summand
`g_i l^2(H)^m`, because `g_i h' h` lies in `g_i H`. Left translation by
`g_i^(-1)` commutes with `r_M` and carries that summand onto `l^2(H)^m`, where
`r_M` is the corresponding operator over `H`. Hence

```text
ker(r_M on l^2(G)^m) = ⊕_i g_i ker(r_M on l^2(H)^m)
                     = N(G) ⊗_(N(H)) ker(r_M on l^2(H)^m),
```

the induced module.

*Correction, 2026-09-12 (lane `review-backlog-2`):* an earlier version used
right cosets `H g_i` and said `r_M` preserves `l^2(H) g_i`. That is false
unless `g_i` normalizes `H`. The claim itself is unaffected.

The von Neumann dimension is invariant under induction (Lück, *L^2-Invariants*,
Theorem 6.29(2)): `dim_(N(G)) (N(G) ⊗_(N(H)) V) = dim_(N(H)) V`. Applying it to
`V = ker(r_M on l^2(H)^m)` gives the stated equality. Integrality when Strong
Atiyah holds for `H` is immediate, since the right side is then an integer.

For the consequence: a matrix `M` over `K[G]` whose support lies in a single
coset-translate of `A`, `B` or `C` is a translate of a matrix over that
subgroup, and translation is a unitary conjugation that does not change kernel
dimension. So an amalgam counterexample must have support meeting both
`A \ C` and `B \ C`. This uses only that `A`, `B`, `C` are subgroups of
`G = A *_C B`; the edge group `C` is arbitrary.
