---
rg: 2
id: periodic-higman-mapping-torus-is-word-hyperbolic
kind: claim
title: The cyclic Higman endomorphism has a word-hyperbolic ascending mapping torus
distinct_from:
  single-free-endomorphism-has-marked-finite-quotients: that asks whether every free-group endomorphism admits compatible marked finite quotients, a residual-finiteness question about the torus; this is a geometric statement about one explicit endomorphism and says nothing about finite quotients.
  non-residually-finite-hyperbolic-group: that is the target of the whole region; this is one hyperbolic family a filling of which might reach it, and on its own it is residually finite by Borisov--Sapir.
---

**ESTABLISHED.**  Let `F = F(a,b,c,d)`, write `x_0 = a, x_1 = b, x_2 = c,
x_3 = d` with indices mod `4`, and define the cyclic Higman endomorphism

```text
phi(x_i) = [x_i, x_(i-1)] = x_i^-1 x_(i-1)^-1 x_i x_(i-1).
```

Let `M_phi = < a,b,c,d,t | t x_i t^-1 = phi(x_i) >` be the ascending mapping
torus.  Then `M_phi` is word-hyperbolic.

Two features make this family worth isolating.

* **It is maximally singular on homology.**  Every generator image is a
  commutator, so `phi_* : H_1(F;Z) -> H_1(F;Z)` is ZERO.  The family therefore
  lies exactly outside the simultaneous full-`H_1`-rank periodization theorems,
  which is why it was not already in this region.
* **The torus itself is not the counterexample.**  Borisov--Sapir prove that
  every mapping torus of an injective free-group endomorphism is residually
  finite.  So `M_phi` is residually finite, and any attempt on
  `non-residually-finite-hyperbolic-group` through this family MUST pass to a
  filling; that is `periodic-higman-deep-torsion-fillings` and
  `periodic-higman-period-spectrum-criterion`.

## Attempts

- Reading hyperbolicity off a train track or a bounded-cancellation estimate:
  unnecessary, since the lower-central-series argument settles the only
  obstruction Mutanguha's criterion leaves.
- Using the homological degeneracy directly: it gives no hyperbolicity, and is
  in fact what puts the family outside the existing periodization results.
