---
rg: 2
id: stw99-xcix-central-copy-transfer-bound-proof
kind: route
title: Combine finite-set embedding transport with the commutator triangle inequality
target: stw99-xcix-central-copy-transfer-bound
requires: []
---

Christensen--Sinclair--Smith--White--Winter, Corollary 4.7 in
[Perturbations of nuclear C*-algebras](https://arxiv.org/abs/0910.4953),
provides an embedding `phi:D -> B` satisfying

```text
||phi(y)-psi(y)|| < 152 sqrt(gamma)    (y in Y).
```

For contractions `x`, `a_x`, and `psi(y)`, expand the commutator as

```text
[phi(y),x]
 = [phi(y)-psi(y),x] + [psi(y),x-a_x] + [psi(y),a_x].
```

The norm of `[r,s]` is at most `2||r||||s||`.  The first two terms are
therefore bounded by `304 sqrt(gamma)` and `2 gamma`, respectively, which
gives the stated inequality.
