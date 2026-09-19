---
rg: 2
id: packet-dressed-shared-implementer-proof
kind: route
title: Compute the induced automorphism and apply Schur factorization
target: packet-dressed-shared-implementer-requires-one-outer-class
requires: []
---

For `b in B`, the relation `u b u^-1=alpha(b)` gives

```text
v b v^-1
 =h u k b k^-1 u^-1 h^-1
 =h alpha(k) alpha(b) alpha(k)^-1 h^-1,
```

which is `(DSI2)`.  Passing to `Out(B)` proves `(DSI3)`, and the converse is
immediate from `v=c u`.

On `T tensor M`, packet words act as `rho_T(B) tensor I_M`; multiplying the
factorization of `rho(u)` on the left and right by `rho(h),rho(k)` proves
`(DSI4)`.  Therefore both dressed words have external factor `R`, whose
commutator with itself is the identity.

Writing `c=h alpha(k)` gives `v=c u`, whence

```text
u v u^(-1)v^(-1)=u c u^(-1)c^(-1)=alpha(c)c^(-1).
```

If the left side is a relator and `B` embeds, then `alpha(c)=c`.  An
implementer `C_alpha` therefore commutes with `rho_T(c)`, so it also commutes
with the packet factor `rho_T(c)C_alpha` of `v`.  No projective packet phase
remains.  Without the commutation relator the commutator is the displayed
single packet word, returning the construction to the finite selector-support
barrier rather than providing a new multiplicity mechanism.

Finally, conjugating an extraspecial Pauli element by another packet element
changes it only by its central commutator.  The induced action on `B/Z(B)` is
therefore the identity for every inner automorphism.  Distinct symplectic
quotient actions cannot be inner-equivalent, proving the Pauli specialization.
