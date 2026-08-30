---
rg: 2
id: stw82-oinfinity-dimension-dichotomy-proof
kind: route
title: Combine absorption permanence with the extension permanence of nuclearity
target: stw82-oinfinity-stable-extensions-obey-maximum
requires: []
artifacts:
  - research/artifacts/stw82-oinfinity-extension-maximum-audit-2026-08-30.md
---

Tensorial absorption by the strongly self-absorbing algebra `O_infinity`
passes from a separable C-star algebra to every ideal and quotient.  This is
the hereditary-subalgebra and quotient permanence in Toms--Winter,
[*Strongly self-absorbing C\*-algebras*](https://arxiv.org/abs/math/0502211),
Corollaries 3.1 and 3.3; `O_infinity` is `K_1`-injective.  Hence `I` and `D`
are `O_infinity`-stable whenever they are nonzero.

For every nonzero separable `O_infinity`-stable algebra `F`,

```text
dim_nuc(F)=1       if F is nuclear,
dim_nuc(F)=infinity otherwise.                         (OD1)
```

Indeed, finite nuclear dimension implies nuclearity.  In the nuclear case,
Bosa--Gabe--Sims--White,
[*The nuclear dimension of O-infinity-stable C\*-algebras*](https://arxiv.org/abs/1906.02066),
Theorem A gives the exact value one for every nonzero separable nuclear
`O_infinity`-stable algebra.  This includes nonunital and projectionless
`F`.  (Equivalently, the lower bound follows because dimension zero is the
AF case, while every nonzero projection in an `O_infinity`-stable algebra is
properly infinite.)  This proves `(OD1)`.

Now apply the nuclearity extension theorem:

```text
E is nuclear  iff  I and D are nuclear.                 (OD2)
```

If `E` is nuclear, `(OD1)` gives dimension one for each nonzero term.  If an
endpoint is zero, the extension is an isomorphism and the maximum formula is
immediate; otherwise all three dimensions equal one.

If `E` is nonnuclear, `(OD2)` makes at least one of `I,D` nonnuclear.  By
`(OD1)` that endpoint and `E` both have infinite nuclear dimension.  Thus
the endpoint maximum and the middle dimension again agree.  These two cases
exhaust the extension and prove the claim.
