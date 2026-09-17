---
rg: 2
id: standard-form-qa-witness-iff-nonhyperlinear-group
kind: claim
title: A standard-form group correlation outside C_qa exists iff a finitely presented non-hyperlinear group exists, and it can always be taken perfect synchronous on a solution group
distinct_from:
  explicit-group-standard-form-correlation-outside-qa: that is the open existence claim (GSQ1); this proves that (GSQ1) is equivalent to the goal as an existence statement, and that its perfect synchronous special case already suffices.
  standard-form-group-separation-collapses-to-corner-model: that shows a perfect synchronous witness is a corner model of its game algebra; this shows that, up to changing the group, every witness of any kind can be replaced by such a corner witness.
  lcs-tracial-ru-gap-equiv-nonhyperlinear: that is the Paddock--Slofstra equivalence for linear systems; this transfers it to standard-form correlations of group von Neumann algebras.
  lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap: that transfers the linear-system gap to graph isomorphism games; this transfers it to vector-state strategies with Alice in L(Gamma) and Bob in L(Gamma)'.
---

**ESTABLISHED** by `standard-form-qa-witness-iff-nonhyperlinear-group-proof`.
This proves no group non-hyperlinear. It fixes how much room the standard-form
route has.

The following are equivalent.

```text
(E1) There is a finitely presented non-hyperlinear group.
(E2) Some finitely presented Lambda has a (GSQ1) witness: PVMs in L(Lambda),
     PVMs in L(Lambda)', and a unit vector xi in l^2(Lambda) whose
     correlation is not in C_qa.
(E3) Some binary linear system Ax=b, with solution group Gamma=Gamma(A,b)
     and central involution J != 1, has a perfect synchronous (GSQ1) witness
     of this form:
       z     = (1 - lambda(J))/2,              tau(z) = 1/2,
       P_(i,phi) = z Pi_(i,phi)(lambda(x)) + delta_(phi,phi_0)(1-z),
       Q_(i,phi) = J_Gamma P_(i,phi) J_Gamma,
       xi    = sqrt(2) z delta_e.
     Here Pi_(i,phi) is the joint spectral projection of the involutions of
     equation i at the local assignment phi, J_Gamma is the modular
     conjugation of l^2(Gamma), and phi_0 is a fixed local assignment.
```

## Consequences

1. **The relaxation gains nothing existentially.**
   - Wave 4 left non-synchronous and imperfect standard-form witnesses as the
     only room beyond the corner-model problem.
   - As a pure existence statement that room is empty. If any witness exists,
     on any group, then a perfect synchronous corner witness exists on a
     solution group.
   - So a proof of (E2) by a non-synchronous witness is, after
     Paddock--Slofstra 5.8, a proof of a tracial/non-`R^U` linear-system gap.
     There is no easier target to aim at.
2. **What is still open.**
   - *Explicitness.* (E1) to (E3) goes through the existence proof of
     Paddock--Slofstra 5.8. Whether a non-synchronous witness is easier to
     *write down* for a given group is not decided here.
   - *Prescribed host.* Whether the witness can be placed in `L(Lambda)`, or
     in `M_k(L(Lambda))`, for the *same* non-hyperlinear `Lambda` is not
     decided here. See `## Attempts` of
     `explicit-group-standard-form-correlation-outside-qa`.
3. **The answer to wave 4's sub-question.**
   - Wave 4 asked: "does every non-hyperlinear `Lambda` admit a (GSQ1)
     witness?" The equivalence part of that question is settled here.
   - Its prescribed-host form stays open.
