---
rg: 2
id: shared-multiplicity-hybrid-row-proof
kind: route
title: Cancel an arbitrary shared multiplicity factor with the D8 role swap
target: shared-multiplicity-commutator-builds-selected-hybrid-row
requires: []
---

On `(C^2_role tensor K) tensor M`, let `j` swap roles and set

```text
e=(|0><0| tensor h+|1><1| tensor I) tensor V.
```

Then `[e,j]=diag(h,h^-1) tensor I_M`; the arbitrary `V` cancels.  For an
involution `h`, its HS rejection energy is exactly `||h-I||_2^2`.

To realize any Boolean predicate, duplicate the finite role/assignment label
set once so the desired diagonal rejection sign has even parity.  Along one
cycle permutation `P`, recursively choose a diagonal sign `S` with
`[S,P]=D_f`.  Both lie in one finite hyperoctahedral group.

Implement the inner automorphisms of `S` and `P` by words `u,v`.  On the
selected tautological isotypic carrier, Schur factorization gives
`u=S tensor R`, `v=P tensor T`, hence

```text
[u,v]=D_f tensor [R,T].
```

The final commutator with the literal role swap cancels `[R,T]` and returns
the predicate rejection phase, so allowed labels satisfy the relator and
rejecting labels pay distance four.  Finite-group exactification makes the
construction robust with fixed constants.  A support-menu packet extends
every exact allowed HALT support, proving completeness on the selected type.
