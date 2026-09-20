---
rg: 2
id: wave3-canonical-k7-class-has-primitive-evaluation
kind: claim
title: The face-zero class of the index-seven GHB7 subgroup evaluates primitively and its finite central detectors are Schur-multiplier quotients
distinct_from:
  wave2-audit-ghb7-cyclotomic-kazhdan-cover: that constructs a rank-six cover from a rationally nonzero integral class; this determines the exact integral evaluation ideal of the specified face-zero class.
  ghb7-centre-survival-iff-unbounded-orbit-cycle-indices: that compares evaluation indices with orbit-cycle indices up to a factor seven; this proves that the initial evaluation index for the canonical K7 class is exactly one and extracts a finite-image restriction.
artifacts:
  - research/artifacts/hyperbolic-rf-wave3-canonical-class-2026-09-20.md
  - experiments/hrf-wave3-canonical-class-2026-09-20/stabilizers.py
  - experiments/hrf-wave3-canonical-class-2026-09-20/stabilizers.json
---

For K=ker(GHB2(7)->C7), a,b,c->1, let c0 be the integral face-zero
cochain pulled back from K\Y, as specified in the wave-2 construction.
Then c0(H_2(K;Z))=Z. Thus the central generator z of B_c0 lies in its
commutator subgroup, and B_c0^ab is naturally K^ab.

For EVERY finite image F of B_c0, put A=<image(z)> and Q=F/A. The
Schur multiplier H_2(Q;Z) surjects onto A, so the central order divides
its exponent. In particular a quotient Q with trivial multiplier
cannot support a nontrivial image of z. No perfectness assumption on
Q is needed for this conclusion.

The exact initial index and finite-family screen do not decide whether
the central orders are bounded over ALL finite images. That question,
and hyperbolic residual finiteness, remain open.
