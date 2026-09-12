---
rg: 2
id: point-norm-approximate-ucp-sections-close-to-exact
kind: claim
title: Point-norm approximate ucp sections of a fixed operator system close to an exact section
distinct_from:
  triangle-relator-extension-admits-local-ucp-sections: that asks for this criterion on every finite-dimensional operator system of one concrete triangle quotient; this is the general closure lemma for a fixed quotient and a fixed operator system.
  finite-reservoir-compactness-lifts-ucp-repairs: that manufactures a lift from finite-dimensional representation packets using RFD and a fixed correction reservoir; this only closes a point-norm limit once approximate liftable maps have already been constructed.
---

**ESTABLISHED.**  Let `pi:A->>Q` be a unital C-star quotient and let `S` be
a finite-dimensional operator system.  Let `phi:S->Q` be ucp.  Suppose that
for every `epsilon>0` there is a ucp map `s_epsilon:S->A` with

```text
||pi o s_epsilon-phi|| <= epsilon.                          (PN1)
```

Then `phi` has a ucp lift `s:S->A` satisfying `pi o s=phi`.

Proof: `point-norm-liftable-ucp-closure-proof`.

Thus local ucp splitting of an extension may be proved by approximate right
inverses on each finite-dimensional operator system; no compatibility between
the approximants at different tolerances is required.  The approximation is
in the operator norm of the finite-dimensional map space, equivalently
uniform point norm on the unit ball of `S`.
