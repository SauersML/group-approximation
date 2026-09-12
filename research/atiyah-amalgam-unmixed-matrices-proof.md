---
rg: 2
id: atiyah-amalgam-unmixed-matrices-proof
kind: route
title: Induction is dimension-preserving, so a subgroup-supported matrix keeps its von Neumann rank
target: atiyah-amalgam-unmixed-matrices-reduce-to-factors
requires: []
---

Let `H <= G` and pick right coset representatives `G = ⊔_i H g_i`. As a left
`H`-set `G` is a disjoint union of copies of `H`, so

```text
l^2(G) ≅ ⊕_i l^2(H) g_i
```

as a Hilbert `N(H)`-module, and right multiplication `r_M` by
`M in M_(m,n)(K[H])` preserves each summand `l^2(H)^m g_i` and acts on it as
the corresponding operator over `H`. Hence

```text
ker(r_M on l^2(G)^m) ≅ ⊕_i ker(r_M on l^2(H)^m) g_i
                     = N(G) ⊗_(N(H)) ker(r_M on l^2(H)^m).
```

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
