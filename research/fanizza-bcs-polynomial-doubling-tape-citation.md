---
rg: 2
id: fanizza-bcs-polynomial-doubling-tape-citation
kind: route
title: Import the projection-doubling recurrence and its polynomial certificates from Fanizza et al.
target: fanizza-bcs-polynomial-doubling-tape
requires:
  - msz-polynomial-doubling-star-algebra-compiler
---

Literature import, verified 2026-08-20 against arXiv:2510.04943v4.
Proposition 5.14 states that

```text
P_tilde_n+X_tilde_n P_tilde_n X_tilde_n-P_tilde_(n+1)
```

vanishes for every `n` in the nonmembership case and has defining-relation
decomposition size at most `C ((n+1)m)^k`. Lines 1160--1172 then invoke the
weighted argument from Mehta--Slofstra--Zhao Proposition 6.3, explicitly use
the convergent series `sum n^k/2^(n/2)`, transfer `D=PQ`, and obtain
`phi(D)<=C_m epsilon`.

The source's definitions identify
`P_tilde_n=Q U^n P U^(-n) Q` and
`X_tilde_n=U^n X_tilde U^(-n)`. The trace-doubling interpretation is an
immediate consequence of the displayed identity and tracial invariance; it
is explanatory, not an additional imported theorem.

The underlying machine algebra and weighted estimate are originally
Mehta--Slofstra--Zhao, arXiv:2312.05617v2, Theorem 4.1 and Proposition 5.3.
Fanizza et al. cite that construction, quantitatively embed it into their
finite BCS family, and reuse the weighted summation.  The prerequisite above
records this provenance without conflating the original additive algebra
with the later BCS packaging.
