---
rg: 2
id: zalesskii-idempotent-trace-rational-citation
kind: route
title: Import Zalesskii's rationality theorem for traces of group-algebra idempotents
target: zalesskii-idempotent-trace-is-rational
requires: []
---

**Source.** A. E. Zalesskii, *On a problem of Kaplansky*, Soviet Math. Dokl.
13 (1972), 449--452. The statement, that the identity coefficient of an
idempotent in `K[G]` lies in the prime field of `K`, is confirmed from
secondary accounts: Gardam's survey talk *Kaplansky's conjectures* (Global
Noncommutative Geometry Seminar, 2021), which quotes it for `C[G]`, and the
literature on the trace of idempotent matrices over group algebras (Math. Z.,
Springer, 2006). The 1972 paper itself was not re-read here.

**Proof idea, as usually presented.** Reduce to a finitely generated subring of
`K` containing the coefficients. Specialize to residue fields of large
characteristic `p`. There `tr(e) = tr(e^(p^k))`, and the Frobenius behaviour of
`p`-th powers of group-algebra elements forces the specialized trace into the
prime field for infinitely many `p`. That pins `tr(e)` to `Q`.
