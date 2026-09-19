---
rg: 2
id: finite-bass-serre-dyadic-three-row-countermodel-proof
kind: route
title: Preserve the dyadic packet in a finite quotient and apply the rectangular capacity inequality
target: finite-bass-serre-dyadic-cell-has-exact-countermodel
requires:
  - finite-bs-selectors-have-marked-fd-countermodels
  - dyadic-pauli-payload-flags-supply-strict-target-capacity
  - rectangular-three-row-cell-forces-double-target-capacity
---

The Pauli flag group in `(BDR1)--(BDR2)` is finite and contains the context
packet injectively.  It is therefore one of the allowed finite packet
amalgams in `finite-bs-selectors-have-marked-fd-countermodels`.  Apply that
claim to the finite list containing this whole packet.  There is a finite
quotient

```text
phi:Gamma -> K                                            (1)
```

which is injective on the packet and does not kill `J`.  Let `rho` be the
left regular representation of `K` composed with `phi`.

Because the packet is injected, its group-algebra projections retain their
canonical traces.  The context assignment projection has identity
coefficient `2^(-(k+1))`; the first Pauli flip splits it evenly.  Hence

```text
q=tr(rho(E))=2^(-(k+2))>0.                              (2)
```

The dyadic flag computation gives, exactly in this representation,

```text
tr(rho(F))=(2-kappa)q,          kappa=2^(1-n).          (3)
```

For arbitrary group words in `(BDR3)`, the four compressed operators are
contractions in the indicated rectangular corners.  Apply
`rectangular-three-row-cell-forces-double-target-capacity` to obtain

```text
kappa q
 <=10sqrt(q)epsilon_0+2sqrt(q)epsilon_1+4eta^2.         (4)
```

Put `delta=max(epsilon_0,epsilon_1,eta)`.  If
`delta>=sqrt(q)`, then `delta>=kappa sqrt(q)/16` because
`0<kappa<=1`.  If `delta<sqrt(q)`, then
`eta^2<=sqrt(q)delta`, and `(4)` gives

```text
kappa q<=16sqrt(q)delta.                                (5)
```

Thus `(BDR4)` holds in both cases.  Squaring the largest of the three
defects proves `(BDR5)`.

Every defining relator of `Gamma` holds exactly under `rho`.  Therefore any
purported dimension-independent estimate making all three defects tend to
zero with presentation energy is refuted at zero energy.  In particular,
the exact identities `(BDR6)` cannot be consequences of the displayed
finite Bass--Serre presentation.
