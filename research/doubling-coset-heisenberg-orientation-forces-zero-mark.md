---
rg: 2
id: doubling-coset-heisenberg-orientation-forces-zero-mark
kind: claim
title: Doubling swaps the marked coset pair and annihilates every integral Heisenberg orientation
distinct_from:
  infinite-order-central-mark-group: that claim is completed by an HNN shear which does not use an equivariant coset pairing; this is the obstruction to the initially proposed direct Heisenberg-lamp replacement.
  finite-covariance-energy-sees-only-character-restrictions: that is an analytic finite-covariance no-go; this is an exact group-action obstruction before approximation theory enters.
  conjugate-local-signs-preserve-marked-carrier: that transports local central words without requiring one global center; this proves that the particular scale-two coset pair cannot carry a torsion-free alternating central phase at all.
---

Let

```text
G=<Gamma,t | t gamma t^-1=alpha(gamma)>,
X=G/Gamma,
```

and suppose `alpha(a)=a^2`.  Put `r=t^-1 a t`.  Then `r^2=a in Gamma`,
so left multiplication by `r` swaps the two points `Gamma,r Gamma`.
Consequently every `G`-invariant alternating pairing

```text
beta : Z^(X) times Z^(X) -> Z
```

satisfies

```text
beta(Gamma,r Gamma)=0.                                 (DHO1)
```

After translating by `t^-1`, the two lamps used by the scale-two
compression witness, `t Gamma` and `a t Gamma`, are precisely this pair.
Therefore a class-two torsion-free Heisenberg lamp group whose commutator
is defined by a `G`-invariant integral alternating form cannot replace the
Clifford sign at doubling scale: its proposed marked commutator is forced to
be trivial.

This does not obstruct the HNN-shear construction of
`heisenberg-hnn-shear-promotes-infinite-defect-to-central-mark`, which
centralizes a new coordinate without asking the coset action to orient a
pair.
