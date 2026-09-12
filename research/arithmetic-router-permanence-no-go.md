---
rg: 2
id: arithmetic-router-permanence-no-go
kind: claim
title: The arithmetic Hull quotient has neither an amenable routing kernel nor an exact finite-model route to soficity
distinct_from:
  arithmetic-defect-saturated-kazhdan-group-is-sofic: That asks for genuinely approximate permutation models of the routed quotient; this proves that amenable routing kernels, LEF models, classical C'(1/6), and virtual specialness cannot supply them.
  sofic-kernel-amenable-quotient-permanence: That is the valid extension theorem with sofic kernel and amenable quotient; here the maps point in the opposite direction, from known source groups onto the unknown quotient, and both routing kernels are in fact nonamenable.
  cprime-one-sixth-presentations-are-hyperlinear: That is the general positive theorem for finite classical C'(1/6) presentations; this applies its stronger residual-finiteness conclusion to exclude such a presentation for the arithmetic full-radical quotient.
artifacts:
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
  - research/artifacts/torsion-free-exact-radical-team-audit-2026-08-26.md
---

Choose the Kazhdan partner in `defect-saturation-from-arithmetic-source` to
be the torsion-free cocompact lattice in `Sp(2,1)` from
`torsion-free-hyperbolic-kazhdan-partner-citation`.  Let

```text
q_H : H ->> Q,                 q_R : R ->> Q
```

be the two maps supplied by the Hull router, where
`R = E * F_2` is the amplified arithmetic source.  Then

```text
ker(q_H) is nonamenable,       ker(q_R) is nonamenable.       (AHK1)
```

Moreover `Q` is not LEF and not residually finite.  Consequently none of the
following can prove its soficity:

1. exact finite multiplication tables for arbitrarily large balls of this
   one fixed `Q`;
2. a cofinal family of genuine finite quotients;
3. a finite classical `C'(1/6)` presentation;
4. a proof that `Q` is hyperbolic virtually special.

The first item is deliberately about **exact** local multiplication.  It does
not exclude soficity: a successful construction must use permutations in
which the relators and products hold only off a vanishing exceptional set.

The amenable-kernel statement is also not an invocation of a quotient
permanence theorem.  Soficity of an ambient group does not in general pass to
its quotient by an amenable normal subgroup; the valid Elek--Szabo theorem in
this repository has a sofic kernel and an amenable quotient.  `(AHK1)` says
that even the tempting but invalid reverse-direction shortcut cannot match
the actual Hull maps.
