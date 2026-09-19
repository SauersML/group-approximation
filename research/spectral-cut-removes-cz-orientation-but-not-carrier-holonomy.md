---
rg: 2
id: spectral-cut-removes-cz-orientation-but-not-carrier-holonomy
kind: claim
title: A multiplicity spectral cut removes the CZ sign but does not authenticate the Leavitt return carrier
distinct_from:
  controlled-fine-reflection-superrank-orientation-law: that classifies the two orientations and measures their mixture; this permits a matrix-coordinate spectral selection and identifies what remains afterward.
  shared-gauge-cz-cancellation-needs-an-identity-outer-anchor: that asks for a word-level cancellation of the whole gauge; this shows that an adaptive nonzero spectral cut cancels the sign locally but does not replace the common-carrier anchor.
  literal-prefix-three-root-swap-retains-typed-carriers: that exhibits separate coarse and fine packet objects; this shows the same separation persists after resolving the fine multiplicity involution into eigenspaces.
artifacts:
  - research/property-t-free-leavitt-full-mf-radical.md
---

**ESTABLISHED MATRIX-COORDINATE AUDIT.**  On the marked two-qubit Pauli
sector, every controlled-fine-reflection implementer has the form

```text
T=C tensor V,             V=V^*=V^(-1),                 (SCO1)
```

where `C=1-2f` is the literal fine-atom reflection and `V` lies in the
external multiplicity algebra.  Let

```text
G_+=(1+V)/2,              G_-=(1-V)/2.                 (SCO2)
```

At least one of these projections is nonzero.  On `S tensor G_+`, `T=C`.
On `S tensor G_-`, `T=-C`; since the Pauli central involution acts as `-I`
on the marked spin sector, the ordinary word `JT` acts there as `C`.
Therefore a finite-matrix selector may always choose a nonzero reducing
fine-packet cut and one of the two fixed words `T,JT` on which the literal
fine reflection is exactly oriented.  No trace, density, PI test, or
superrank estimate is needed for this local orientation step.

This does **not** authenticate the coarse-to-fine support row.  Let `W` be
the Whitehead/partial-swap actuator.  Nothing in the controlled Pauli
covariance forces

```text
[W,G_+]=0             or             [W,G_-]=0.          (SCO3)
```

Pulling a selected target cut back by `W` gives `W^*G_+W` or `W^*G_-W` in
the source leaf.  Extending that projection across the coarse matrix units
produces a legitimate **source** multiplicity cut, but it does not identify
the resulting coarse carrier with the selected **fine** carrier.  In the
typed rectangular model the two extensions have dimensions `2 rank(G)` and
`4 rank(G)` respectively, while the one leaf transported by `W` has equal
rank on both sides.  Thus the rectangular escape survives on each selected
orientation.

Consequently the arbitrary sign of `V` is not itself the operator-norm
obstruction.  After adaptive spectral selection the exact missing assertion
is preservation/return of one nonzero selected gauge cut by the mixed
Leavitt actuator, equivalently the same-carrier holonomy relation.  Treating
orientation as still open overstates the residue; treating the spectral cut
as a common carrier is invalid.

