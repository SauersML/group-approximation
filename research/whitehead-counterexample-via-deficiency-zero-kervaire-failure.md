---
rg: 2
id: whitehead-counterexample-via-deficiency-zero-kervaire-failure
kind: route
title: A deficiency-zero Kervaire killing failure is a finite non-aspherical subcomplex of a contractible 2-complex
target: nonaspherical-subcomplex-of-contractible-2-complex-exists
requires:
  - kervaire-killing-failure-over-deficiency-zero-group-exists
  - deficiency-zero-kervaire-failure-yields-whitehead-counterexample
artifacts:
  - research/artifacts/ideas-bridges-2026-09-13.md
---

Take the failure `(G, w)` given by `kervaire-killing-failure-over-deficiency-zero-group-exists`.
Item 2 of `deficiency-zero-kervaire-failure-yields-whitehead-counterexample`
shows:
- the presentation complex `L` of `<X, t | R, W>` is a finite contractible
  2-complex;
- the presentation complex `K` of `G` is a connected subcomplex of `L` with
  `pi_2(K) != 0`.

That is exactly the statement of the target, with `Y = L`.
