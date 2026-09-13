---
rg: 2
id: bernoulli-collapse-iff-a-bernoulli-shift-is-its-own-square
kind: claim
title: Base entropy fails to classify Bernoulli shifts over a group exactly when some finite-entropy Bernoulli shift is isomorphic to its own square
distinct_from:
  bernoulli-isomorphism-collapse-set-is-a-subgroup: that proves failure is absorption X_h ≅ X_h × X_d for some d; this sharpens it to the single Leavitt-type relation X ≅ X × X on one Bernoulli shift.
  leavitt-module-dual-actions-are-self-squares-off-bernoulli: that is the algebraic self-square X_L ≅ X_L² over the binary Leavitt units, which is not a Bernoulli factor; this says a failure of classification is exactly a Bernoulli shift with the same self-square property.
---

**ESTABLISHED** by [[bernoulli-collapse-iff-own-square-proof]].

Let `G` be a countably infinite group and `X_h` the Bernoulli class of base entropy `h`. The following are
equivalent:

1. base entropy fails to classify Bernoulli shifts over `G`, that is `D(G) != {0}` in
   `bernoulli-isomorphism-collapse-set-is-a-subgroup`;
2. `X_h ≅ X_h × X_h` for some `0 < h < ∞`.

When they hold, `X_h ≅ X_h^k` for every `k >= 1`, and the witnesses `h` in (2) are unbounded.

**Reading.**
- A failure of classification is a *measurable Leavitt relation* on a Bernoulli shift: one Bernoulli shift
  is two independent copies of itself.
- The binary Leavitt unit group already carries an exact algebraic self-square
  (`leavitt-module-dual-actions-are-self-squares-off-bernoulli`). The negative direction over it asks to make
  such a self-square Bernoulli, and the stabilizer test shows that the algebraic one cannot be.
- By `bernoulli-entropy-counterexample-constraints` (b), a self-square `X_h` forces `h^Rok_sup(G) <= h`.
