---
rg: 2
id: nonru-bcs-group-factor-via-phase-surviving-local-colimit
kind: route
title: A phase-surviving local colimit puts the tracial non-RU system in a corner of its group factor
target: non-ru-bcs-is-satisfiable-in-a-group-factor
requires:
  - finite-readout-bcs-decoders-are-phase-surviving-local-colimits
  - tracial-nonru-bcs-has-phase-surviving-local-colimit
---

Take finite local data `D` for `B_*` with `J` of order `n` in `Lambda(D)`, as in
`tracial-nonru-bcs-has-phase-surviving-local-colimit`. By (LC1) of
`finite-readout-bcs-decoders-are-phase-surviving-local-colimits` the images of
the local involutions give a unital *-homomorphism

```text
A(B_*) -> C[Lambda(D)] p_omega  subset  p_omega L(Lambda(D)) p_omega,
```

and `p_omega` is a nonzero central projection by Lemma 0 of that proof. This
is the corner form of `(GFB1)` allowed in
`non-ru-bcs-is-satisfiable-in-a-group-factor`, with host
`Lambda = Lambda(D)`. By (LC2) and (LC3) the host is finitely presented and
`J^(n/p)` lies in its finite residual for some prime `p | n`.
