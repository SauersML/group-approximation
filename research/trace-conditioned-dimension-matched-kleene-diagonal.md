---
rg: 2
id: trace-conditioned-dimension-matched-kleene-diagonal
kind: claim
title: Dimension-matched Kleene soundness may use finitely many canonical-trace tests
distinct_from:
  dimension-matched-kleene-microstate-diagonal: that searches only relator defect and marked distance; this also requires a finite character/moment profile known to hold in the canonical trace.
  instance-modulated-kleene-microstate-diagonal: that lets collapse constants depend computably on the source program; this adds finite canonical-trace side conditions rather than changing those constants.
  finite-schur-clifford-packet-flexible-hs-exactification: that corrects one approximate finite packet; this explains why the fixed-point search may additionally insist that its exactified packet have near-regular character multiplicities.
---

Suppose a computable compiler assigns to every program `M` a finite
presentation `G_M=<S_M|R_M>`, a word `w_M`, computable constants
`delta_M>0` and `alpha_M<sqrt(2)`, and finitely many words and targets

```text
(t_(M,i),c_(M,i),eta_(M,i)),       1<=i<=r_M.           (TDM1)
```

Assume:

1. if `M` does not halt, then `w_M!=1` and the canonical group trace obeys
   `tau_(G_M)(t_(M,i))=c_(M,i)`;
2. if `M` halts and prints `d`, no `d`-dimensional tuple simultaneously has

```text
Def_(R_M)(U)<delta_M,
||w_M(U)-I||_2>alpha_M,
|tr(t_(M,i)(U))-c_(M,i)|<eta_(M,i)  for every i.        (TDM2)
```

Then one can effectively construct a finitely presented nonhyperlinear
group.

In particular the side tests may force a fixed finite control subgroup to
have nearly its regular character profile.  This removes arbitrary local
finite-type concentration from a candidate canonical microstate, although it
does not align independently named context carriers.
