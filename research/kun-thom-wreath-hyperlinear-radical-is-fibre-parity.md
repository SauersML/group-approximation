---
rg: 2
id: kun-thom-wreath-hyperlinear-radical-is-fibre-parity
kind: claim
title: The hyperlinear and sofic radicals of every Kun--Thom binary wreath equal its finite residual and fibre-parity kernel
distinct_from:
  kun-thom-wreath-sofic-radical-is-fibre-parity-kernel: "That computes the sofic radical and its residually finite quotient; this adds the exact hyperlinear radical by killing every fibre pair in every tracial matrix-ultraproduct homomorphism."
  kun-thom-wreath-family-is-not-hyperlinear: "That exhibits one nontrivial collapsed lamp for each parameter choice; this computes the entire kernel invisible to hyperlinear groups and identifies its universal residually finite quotient."
  compression-wreath-five-radicals-coincide: "That concerns the separate doubling family and its operator-norm, linear and compact residuals; this concerns the Kun--Thom Theorem E family and the hyperlinear radical, without asserting an operator-norm radical formula."
artifacts:
  - research/artifacts/kun-thom-exact-hyperlinear-radical-2026-09-20.md
---

For every prime power q and every r,d>=3, put

```
R_+=F_q[x_1,...,x_d], R=F_q[x_1^(+-1),...,x_d^(+-1)],
Gamma=EL_r(R_+), G=EL_r(R) rtimes SL_d(Z),
N=<<Gamma>>_G=EL_r(R), X=G/Gamma,
W=(direct_sum_X C_2) rtimes G.
```

Let K be the subgroup of finitely supported binary lamp configurations
having even parity in every fibre of `X -> G/N`. Then

```
Rad_hyp(W) = K = Rad_sof(W) = Res_fin(W).
```

Here each approximation radical intersects kernels of all homomorphisms
to groups in that class, and `Res_fin` intersects kernels of all finite
quotients. Equivalently for `Rad_hyp`, intersect kernels of all
homomorphisms into unitary groups of tracial matrix ultraproducts, without
any trace or injectivity assumption.

The quotient is exactly

```
W/K = (direct_sum_(G/N) C_2) rtimes G,
```

with quotient map given by summing lamps over fibres. It is residually
finite. Thus every map from W to a hyperlinear group factors uniquely
through this same explicit residually finite quotient. The conclusion
includes Jihao Liu's q=2, r=d=3 wreath, but is not limited to it.

## Attribution

Gabor Kun and Andreas Thom supply the group family and compression
mechanism in [*Nonsofic wreath products of residually finite groups*](https://arxiv.org/abs/2608.06222),
Theorem E. The analytic input is Jihao Liu,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 1.2/6.7, together with Andreas Thom's conditional
normalization theorem, [Theorem 1.2](https://andreasthom.github.io/pdf/nonhyperlinear.pdf).
Liu's Theorem 1.3/7.4 gives another normalization route and credits Thom.
This exact radical formula is a downstream deduction using the existing
Cairn fibre-parity theorem; it is not quoted as Liu's Theorem 8.3 or
claimed to be an independently discovered analytic theorem.

## Attempts

2026-09-20: checked every fibre pair is killed by the all-trace normalization
premise, then independently checked the finite-quotient separation needed
for the reverse inclusion. The route retains the normalization,
Kun--Thom structural theorem and existing exact fibre-parity theorem as
explicit dependencies; it introduces no empty-premise analytic import.
