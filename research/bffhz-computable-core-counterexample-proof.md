---
rg: 2
id: bffhz-computable-core-counterexample-proof
kind: route
title: Use MIF faithfulness and finite-presentation reflection on the regular cyclic twisted core
target: bffhz-computable-core-fp-upgrade-is-false
requires:
  - relative-automorphism-fp-host-reflects-base-presentation
  - regular-cyclic-twisted-core-is-decidable-mif-non-fp
artifacts:
  - research/artifacts/boone-higman-relative-automorphism-fp-obstruction-2026-09-08.md
---

For any MIF group S, the evaluation action on Hom_S(S*F_n,S) is faithful.
Indeed, a nonidentity relative automorphism alpha moves some x_j. The
nonidentity word x_j^-1 alpha(x_j) cannot vanish under every evaluation
into S, by the definition of MIF. An evaluation detecting it is moved
by alpha. This is the proof of
[BFFHZ Lemma 2.2](https://arxiv.org/html/2503.21882v2).

Apply this to the group T supplied by
`regular-cyclic-twisted-core-is-decidable-mif-non-fp`. It gives K=1.
If A/K=A were finitely presented,
`relative-automorphism-fp-host-reflects-base-presentation`, applied to
its canonical translation copy of T, would imply that T is finitely
presented. This contradicts the pair-orbit obstruction for that group.
All the computable-core hypotheses in the refuted claim hold for T.

For the more general equivalence, an infinite simple S is centerless.
The same faithfulness argument identifies the action image with A, and
the necessary and sufficient conditions for the full A in
`relative-automorphism-fp-host-reflects-base-presentation` apply.

The published Question 3.2 restricts the base to finitely presented
simple groups and is therefore not contradicted by this example.
