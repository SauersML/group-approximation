---
rg: 2
id: tensor-gaussian-binary-wreath-equivalence-proof
kind: route
title: Pass from binary coefficients to relative embeddings and from free lamps to Gaussian signs
target: binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
requires:
  - binary-coset-lamp-coefficient-forces-relative-embedding
  - relatively-embeddable-pair-makes-the-hnn-group-hyperlinear
  - hnn-stable-letter-rounds-to-finite-order
artifacts:
  - research/artifacts/tensor-swap-expectation-repair-2026-09-07.md
---

The ordinary binary wreath supplies a centered lamp with the coset
coefficient. The first prerequisite gives scalar relative embeddability;
the second constructs a canonical HNN model; the third supplies its free
binary sign, proving hyperlinearity of the free binary wreath.

Conversely, in the CE canonical algebra of the free binary wreath, use

```text
v_(x,k)(t)=(exp(i t s_x/sqrt(k)))^tensor k,
U_k(g)=u_g^tensor k.
```

The second-order one-coordinate trace expansion gives the joint
characteristic function of independent standard Gaussians after taking
the `k`th power. Commutator traces tend to one, so the limiting lamps
commute. Covariance with the diagonal actor is exact. Every mixed word
with actor `g!=e` has trace bounded by `(C/sqrt(k))^k`, so the limit has the
canonical Gaussian crossed-product trace. The separable limit remains CE
by diagonalizing finite tensor-power matrix models. Independent Gaussian
signs realize the ordinary binary wreath canonically.

The artifact proves the uniform fixed-word expansion, boundedness,
commutation, crossed-product trace, and both passages to canonical binary
lamps. It proves neither hyperlinearity nor its failure for an unresolved
candidate pair.

For the remaining equivalent conditions, the direct factor-swap construction
in Section 5 of the artifact gives
`D hyperlinear iff E hyperlinear`; restriction proves one direction and
the two-block matrix construction proves the other. The first prerequisite
gives `E hyperlinear => RE/scalars`. The HNN criterion and finite-order
rounding give `RE/scalars => H hyperlinear => E hyperlinear`, while the
enlarged-double case of the HNN criterion gives `RE/scalars iff Dplus
hyperlinear`. This closes the entire seven-condition equivalence without
Gao's printed plain-double converse or any relative-Haar assumption.
