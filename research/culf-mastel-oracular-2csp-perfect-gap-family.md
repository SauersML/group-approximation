---
rg: 2
id: culf-mastel-oracular-2csp-perfect-gap-family
kind: claim
title: Culf--Mastel give a computable finite oracular 2-CSP family with perfect CE completeness and a constant CE soundness gap
distinct_from:
  oracularizable-tracial-nonru-game-exists: that freezes one non-RU game by applying the Fu--Mastel--Zhang incidence conversion; this records the machine-indexed Culf--Mastel family in the orientation needed by reverse Kleene.
  perfect-completeness-constant-soundness-lcs-compiler: that asks for affine LCS syntax and a solution-group central sign; this source has general 2-CSP predicates and no ordinary-group mark.
---

There is a total computable map from a Turing-machine index `m` to a finite,
non-succinct 2-CSP `B_m` and a constant `s<1`, independent of `m`, such that

```text
m halts      => inf_tau def_(B_m)(tau)=0,
m nonhalts   => inf_tau def_(B_m)(tau)>1-s,                 (CMG1)
```

where the infima are over finite-dimensional traces, equivalently over
Connes-embeddable traces.  On the completeness side, a sequence with defect
tending to zero gives a perfect trace in a tracial matrix ultraproduct.  The
perfect strategy is oracularizable: the measurements attached to every
question pair which is jointly queried commute.  Thus `(CMG1)` has the exact
operator-algebraic form

```text
HALT       => B_m has a perfect CE tracial model,
NONHALT    => B_m has no perfect CE tracial model.           (CMG2)
```

This is Culf--Mastel, arXiv:2410.21223v2, Definition 4.11, Theorem 4.14,
Corollaries 4.16 and 4.18, together with Lemma 6.3 and Corollary 6.4.  The
passage from succinct to finite instances in Corollary 4.18 is a total
exponential-time reduction, which is all a recursion-theorem construction
needs.

The statement does not groupify the predicates.  In particular it supplies
neither an LCS central involution nor a canonical group-algebra corner.
