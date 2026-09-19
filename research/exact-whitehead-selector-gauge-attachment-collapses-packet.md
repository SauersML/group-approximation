---
rg: 2
id: exact-whitehead-selector-gauge-attachment-collapses-packet
kind: claim
title: Exact same-carrier attachment of Whitehead gauges to the unequal selectors collapses the finite packet
artifacts:
  - research/exact-whitehead-selector-gauge-attachment-collapse-proof.md
distinct_from:
  unequal-label-ranks-forbid-relational-reservoir-conjugacy: that rules out cancelling separated unequal label factors to deduce reservoir conjugacy; this allows the gauges to be exposed by identity-outer anchors and proves that adjoining both exact selector covariances on the same literal packet carrier collapses that carrier.
  same-center-whitehead-gram-is-not-native-selector-gram: that refutes one proposed occurrence identification; this gives the general regular-trace firewall for every exact fixed-word identification on the whole packet isotypic carrier.
  binary-leavitt-native-two-scale-cross-gram-positive: that asks only for a positive representation-dependent reducing subcorner extracted in finite matrices; this proves why replacing that subcorner by the fixed full packet carrier is too strong.
---

Let `B<=Gamma` be a finite subgroup and let `e in C[B]` be the central
isotypic projection of a `d`-dimensional irreducible `B`-module.  Assume
`B` embeds in `Gamma`, so in the canonical group trace

```text
tau(e)=d^2/|B|>0.                                      (EWS1)
```

On `eL(Gamma)e`, identify the `B`-action as

```text
M_d(C) tensor I_M.                                    (EWS2)
```

Suppose fixed group words give two Whitehead transports whose label parts
have been removed by literal packet words, exposing multiplicity
involutions `V_1,V_2`.  Allow any exact word mechanism making these two
involutions unitarily conjugate in the `B`-commutant.  Suppose further that
fixed selector words and fixed support rows preserve `e` and give, on this
same carrier, the two exact normal forms

```text
U_i R_i U_i^*=C_(q_i) tensor V_i,

(r_1,q_1)=(1/2,1/4),       (r_2,q_2)=(1/4,1/8),       (EWS3)
```

where `R_i` has label negative fraction `r_i` and `C_(q_i)` has label
negative fraction `q_i`.

Then `e=0` in `L(Gamma)`.  Consequently `(EWS1)` fails: no group containing
the finite packet `B` can satisfy all these identities on its literal full
isotypic carrier.

Indeed, conjugacy of `V_1,V_2` gives one common positive spectral fraction
`theta`.  The first row of `(EWS3)` forces

```text
theta=1/2,
```

while the second forces

```text
theta=5/6.
```

The contradiction applies inside every nonzero finite tracial corner, in
particular inside `eL(Gamma)e`.  Faithfulness of the canonical trace then
forces `e=0`.

This is the exact regular-representation firewall for wordizing the missing
occurrence seam.  It still permits the useful algebraic identity

```text
(A_i^(-1)W_i)|_e=I_d tensor V_i,
```

whenever a literal packet word `A_i` removes the Whitehead label action.
Multiplying this identity-outer anchor by a packet label reflection also
formally produces `C_(q_i) tensor V_i`.  What cannot be imposed while the
packet remains embedded is that both resulting unequal selector rows act
on the whole fixed carrier `e` as in `(EWS3)`.

Therefore a valid property-`(T)`-free bridge must be genuinely
finite-matrix-only: it must extract a positive reducing subcorner depending
on the matrix model, align the gauges only there, and charge the discarded
mass by ordinary word defects.  A fixed packet enlargement, fixed
identity-outer anchor, or exact whole-isotypic support identity cannot
replace the open cross-Gram/occurrence estimate.

DERIVATION
exact-whitehead-selector-gauge-attachment-collapse-proof
