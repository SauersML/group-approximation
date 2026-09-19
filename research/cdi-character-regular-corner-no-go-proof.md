---
rg: 2
id: cdi-character-regular-corner-no-go-proof
kind: route
title: Compute the canonical coefficients of central sectors, restrictions, and finite-support corners
target: cdi-character-cannot-be-promoted-by-regular-corners
requires:
  - cdi-property-t-envelope-has-nonabelian-base
---

Pass to a torsion-free finite-index subgroup of a cocompact lattice in
`Sp(n,1)`.  It remains hyperbolic and property `(T)`, so CDI Theorem A(1)
still applies; it is ICC because it is a non-elementary torsion-free
hyperbolic group.  It is linear and finitely generated, hence residually
finite by Mal'cev.  Its canonical character `delta_H` is CE.  Therefore the
CDI character `chi` is not `delta_H`, since its GNS algebra contains the fixed
non-CE input.

For a finite central extension and a lift `h_tilde` of `h!=e`, every term
`c h_tilde`, `c in C`, is a nonidentity group element.  The canonical group
trace vanishes on all of them, so

```text
tau_Htilde(q_beta h_tilde)=0.                          (CDI-R1)
```

At `h=e` the normalized value is one.  This is exactly the canonical trace
on the `beta`-twisted group algebra of `H`, not the prescribed `chi`.

If `H<=Gamma`, decompose `ell^2(Gamma)` over left `H`-orbits.  On each orbit
the restricted left-regular action is unitarily equivalent to `lambda_H`.
Thus canonical restriction and multiplicity compression do not change
`delta_H`.  An induced representation built from `pi_chi` has deliberately
replaced these regular orbit blocks; calling it induced supplies no
identification with the canonical regular representation.

First note that unitarity forces the commutation hypothesis.  If `qhq` is a
unitary of `qL(Gamma)q`, then

```text
q (hqh*) q=q.
```

For the projections `q` and `p=hqh*`, the equality `qpq=q` gives `q<=p`.
The finite canonical trace gives `tau(q)=tau(p)`, so faithfulness forces
`q=p`.  Applying this to every `h` gives `[q,H]=0`.

Now write `q=sum_(g in F) a_g g` with `F` finite.  Then

```text
tau_Gamma(qh)=a_(h^-1).                                (CDI-R2)
```

Because `q` commutes with `H`, `chi_q` is a normalized tracial character of
`H`.  Equation `(CDI-R2)` gives finite support.  If it were nonzero at
`h!=e`, conjugation invariance would make it nonzero on the infinite
`H`-conjugacy class of `h`, contradicting finite support.  Since
`chi_q(e)=1`, it equals `delta_H`.

Finally, the regular action `H` on itself has exact finite models from finite
quotients of the residually finite group.  Standard wreath-product
permanence (equivalently the regular-action case of the sofic-action wreath
theorem) makes every finite-lamp restricted wreath product sofic.  Its group
factor and all canonical positive corners are CE.  A Clifford central cut
has coefficient formula `(CDI-R1)`; it changes the multiplier, not the
underlying regular trace.  Hence non-CE of `pi_chi(H)''` does not pass without
an additional algebraic map or recoverability theorem.
