---
rg: 2
id: agent-aggregate-escape-two-intertwiner-clifford-proof
kind: route
title: Apply Clifford theory and cancel the packet multiplier on multiplicity space
target: agent-aggregate-escape-two-intertwiner-clifford-dichotomy
requires:
  - agent-aggregate-escape-rfd-support-orientation-firewall
  - agent-aggregate-escape-finite-packet-actor-no-go
---

Because `F` is finite, the orbit of `sigma` under `Q` is finite.  On the
`sigma`-isotypic summand of any covariant representation, Schur's lemma
writes a stabilizer intertwiner as

```text
V_q tensor M_q.
```

Associativity and `(TCF1)` force

```text
M_q M_r=omega(q,r)^(-1)M_(qr),                          (1)
```

including every relation inherited from `R`.  Thus the multiplicity
operators form a representation of `(TCF2)`.  This proves necessity.

Conversely, tensor the packet intertwiners with any solution of `(1)`.  The
two multipliers cancel, giving an honest representation of the stabilizer.
Induce it across the finite coset set `Q/Q_sigma`; `F` acts on each orbit
summand by the corresponding conjugate of `sigma`, and `Q` permutes the
summands.  This proves sufficiency and keeps the dimension finite.

When `omega` and the relevant holonomy factor through a finite group `H`,
the vector space with basis `{delta_h:h in H}` carries the inverse-twisted
regular operators

```text
L_q^(omega^(-1)) delta_h
  =omega(q,h)^(-1) delta_(qh),                          (2)
```

after the standard harmless normalization convention for cocycles.  Equation
`(2)` satisfies `(1)`, so the marked type extends.  Orbit summing, tensoring
with `(2)`, and taking direct sums are exact operations; none produces
presentation energy which could pay the positive marked corner.

Finally, the central extension `Q_sigma^omega` rewrites projective
representations as honest representations with a prescribed central
character.  Absence of `(TCF2)` is precisely finite-dimensional invisibility
of that character.  A normalized-HS estimate for approximate solutions is
precisely the quantitative projective fd-radical modulus claimed in the
statement.
