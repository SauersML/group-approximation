---
rg: 2
id: finite-overgroup-character-packing-is-hyperlinearity-conservative
kind: claim
title: Finite-overgroup character packing cannot create nonhyperlinearity from a hyperlinear base
root: true
artifacts:
  - research/finite-overgroup-character-packing-is-hyperlinearity-conservative-proof.md
distinct_from:
  finite-selector-gadget-induction-barrier: that shows every marked selector character occurs in some representation of one finite overgroup; this proves preservation for the entire group obtained by attaching any finite family of such overgroups.
  simultaneous-character-packing-removes-max-loss: that is the valid matrix-capacity contradiction once a sufficiently large simultaneous packing exists; this locates exactly why finite Bass--Serre attachments cannot supply such a contradiction over a hyperlinear base.
---

Let `Gamma` be countable.  For finitely many finite subgroups `H_i<=Gamma`,
choose finite overgroups `H_i<=G_i` and form the iterated amalgam

```text
Gamma_hat
  =Gamma *_(H_1) G_1 *_(H_2) G_2 * ... *_(H_m) G_m.    (FOC1)
```

If `Gamma` is hyperlinear, then `Gamma_hat` is hyperlinear.  The same holds
for any finite graph of groups whose distinguished vertex is `Gamma`, whose
other vertex groups are finite, and whose edge groups are finite.

Consequently a collection of finite overgroups containing context groups,
even if it gives many orthogonal conjugates of selected character
idempotents and admits a prescribed noncanonical tracial extension, cannot
be an independent source of nonhyperlinearity.  If the resulting group is
nonhyperlinear, then the base `Gamma` was already nonhyperlinear.

In matrix-ultraproduct terms, every canonical embedding of `Gamma` extends
through the finite graph.  The restriction of a canonical embedding to a
finite edge group is the normalized regular representation.  A regular copy
of each finite vertex group has the same edge restriction, and matching
finite-dimensional trace-preserving embeddings supplies the required edge
unitaries.

Thus a character-packing construction capable of proving a new
nonhyperlinearity result must add a relation not contained in finite
Bass--Serre covariance.  It must constrain several edge intertwiners jointly
on their multiplicity spaces, or place the packing inside a vertex whose
hyperlinearity is itself the load-bearing question.
