---
rg: 2
id: harris-three-dimensional-lp-llp-proof
kind: route
title: Compose Harris's LP normal form with the PRS obstruction
target: lp-of-harris-generator-system-forces-nonhyperlinear
requires:
  - harris-lp-to-llp-implication-is-one-directional
  - llp-regular-dominating-completion-forces-nonhyperlinear
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
---

## Composition proof

Let `A=C^*_pi(G)` and let `S_pi` be Harris's three-dimensional hyperrigid
generator system.  The surviving direction of Harris's criterion, recorded
in `harris-lp-to-llp-implication-is-one-directional`, is

```text
LP(S_pi) => LLP(C^*_pi(G)).
```

If in addition `lambda_G` is weakly contained in `pi` and `pi` is
nonamenable, then LP of `S_pi` gives LLP of `C^*_pi(G)`.  The established
Paulsen--Rahaman--Samei obstruction
`llp-regular-dominating-completion-forces-nonhyperlinear` therefore gives
that `G` is not hyperlinear.

Taking `pi=lambda_G` for a finitely generated nonamenable group is the
stated reduced-completion specialization.  No converse is used or asserted:
LP of this finite-dimensional Harris system is a sufficient, potentially
strictly stronger, hypothesis than ambient LLP.
