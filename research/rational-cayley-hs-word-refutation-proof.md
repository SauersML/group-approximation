---
rg: 2
id: rational-cayley-hs-word-refutation-proof
kind: route
title: Preserve a strict word-energy violation in a dense rational Cayley chart
target: failed-hs-word-bounds-have-rational-witnesses
requires: []
artifacts:
  - research/artifacts/hs-word-certificate-rational-search.md
  - experiments/hs_word_certificate.py
---

For skew-Hermitian K, I+K is invertible and (I-K)(I+K)^(-1) is unitary.
The inverse parametrization covers all unitaries without eigenvalue -1;
these are dense. Rational skew-Hermitian parameters therefore give a
dense exactly unitary family in each fixed dimension.

The difference between the marked energy and the proposed multiple of
the finite relator sum is continuous. A strict violation survives on a
rational Cayley tuple, where the energies and their comparison are exact
rationals. Enumerate dimensions, common denominators and integer
parameter vectors by finite increasing stages. Every rational tuple is
eventually visited, so a violated coefficient is eventually refuted.

The artifact supplies the full argument and the executable's trust
boundary. Its tests are finite controls, not the proof of density or a
proof of any all-dimensions inequality.
