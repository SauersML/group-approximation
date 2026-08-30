---
rg: 2
id: stw99-problem-lxii-kk-uniqueness
kind: claim
title: Vanishing KK class gives strong asymptotic unitary equivalence for absorbing representations (STW Problem LXII)
root: true
artifacts:
  - research/artifacts/stw62-kk-uniqueness-literature-import-2026-08-30.md
---

Let `A` be a separable C-star algebra and let `B` be a sigma-unital stable
C-star algebra.  Suppose that

```text
phi, psi : A -> M(B)
```

are absorbing representations forming a Cuntz pair, so
`phi(a)-psi(a) in B` for every `a in A`.  If

```text
[phi,psi] = 0 in KK(A,B),
```

then `phi` and `psi` are strongly asymptotically unitarily equivalent:
there is a norm-continuous path `u:[0,infinity)->U(1+B)` with `u(0)=1` and

```text
lim_(t->infinity) ||u(t) phi(a) u(t)^* - psi(a)|| = 0
```

for every `a in A`.  Conversely, such a path forces the Cuntz-pair class to
vanish.

This is the affirmative solution of STW Problem LXII.  Gabor Szabo proves it
in *The uniqueness theorem for Kasparov theory*, arXiv:2601.23029; the STW
v2 addendum records the problem as solved.
