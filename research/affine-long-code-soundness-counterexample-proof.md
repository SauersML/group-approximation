---
rg: 2
id: affine-long-code-soundness-counterexample-proof
kind: route
title: Decode each query direction and read the shared zero coset in the shifted game
target: affine-long-code-test-has-no-uniform-soundness
requires:
  - affine-shift-games-have-vanishing-value
  - noisy-affine-direction-decoding-over-cyclic-alphabets
artifacts:
  - research/artifacts/unique-games-affine-test-soundness-2026-09-07.md
  - scripts/check_unique_games_affine_soundness.py
  - research/artifacts/unique-games-affine-test-replay-2026-09-07.json
---

The prerequisites give the explicit low-value source game and the noisy
direction decoder. Set `F_u(Y)=Y_(u bhat(Y)^2)`. Sections 4--6 prove
that these are valid folded output labelings and evaluate their acceptance.
On correct decoding of edge `(u,b)`, the selected coordinate `u b^2`
projects to the shared zero coset. The two ideal outputs therefore have
equality probability `1/m+(1-1/m)rho^3`, by the composition of three
symmetric noise kernels. The probability either actual output differs
from its ideal output is at most twice the decoder error. This proves
the displayed lower bound without conditioning on decoding success.

The source value bound and exponential error decay prove the parameter
claim; Section 7 gives the exact rational finite-gap calculation. The
artifact explicitly converts folding into permutation constraints and
discusses finite weights, regularity, and the scope of the obstruction.
Cairn tracks these dependencies; the proof is mathematical, with exact
finite regression checks rather than proof-assistant verification.
