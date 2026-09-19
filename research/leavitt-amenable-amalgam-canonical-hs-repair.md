---
rg: 2
id: leavitt-amenable-amalgam-canonical-hs-repair
kind: claim
title: Repair canonical microstates of the two amenable Leavitt faces by vanishing HS perturbations
refuted_by: leavitt-amalgam-microstates-have-unrepairable-kernel
distinct_from:
  leavitt-one-compressor-join-is-proper-amalgam-quotient: that proves the natural amalgam map has nonzero kernel but does not itself formulate a matrix repair; this asks to kill that kernel by o(1)-HS changes to canonical amalgam models.
  leavitt-first-mixed-amenable-face-relator: that identifies the first explicit mixed base-face kernel word; this asks for simultaneous asymptotic repair of every fixed quotient relation while retaining canonical trace separation.
  reduced-amalgam-canonical-trace-is-mf: that asks for operator-norm MF trace selection on a different Kun--Thom double; this is a normalized-HS quotient-repair proposal for the literal Leavitt one-compressor join.
---

Let

```text
G = Lambda_(L_0) *_(Lambda_(L_0) cap Lambda_P) Lambda_P,
q:G -> J=<L,tau,c>.
```

Starting from canonical sofic/hyperlinear microstates of the amenable-factor
amalgam `G`, perturb the two factor generator tuples by `o(1)` in normalized
Hilbert--Schmidt norm so that:

1. every fixed word in `ker q` has defect tending to zero;
2. every fixed nontrivial element of `J` remains asymptotically traceless.

Such repaired tuples would be canonical hyperlinear microstates of `J`.

This proposal is refuted. A nontrivial kernel word has canonical trace zero in
`G`, hence is asymptotically `sqrt(2)` from the identity, and a vanishing HS
change of a fixed generator tuple changes its evaluated fixed word by only
`o(1)`. See `leavitt-amalgam-microstates-have-unrepairable-kernel`.
