---
rg: 2
id: kun-thom-wreath-hyperlinear-radical-proof
kind: route
title: Normalize every lamp model, telescope all fibre pairs, and separate the quotient by finite groups
target: kun-thom-wreath-hyperlinear-radical-is-fibre-parity
requires:
  - kazhdan-compression-pairs-normalize-all-tracial-models
  - kun-thom-nonsofic-wreath
  - kun-thom-wreath-sofic-radical-is-fibre-parity-kernel
artifacts:
  - research/artifacts/kun-thom-exact-hyperlinear-radical-2026-09-20.md
---

Use the full parameter family of the target. The Kun--Thom prerequisite
makes Gamma and G finitely generated Kazhdan groups, with compression
semigroup generating G. Expressing a finite generating set in that
semigroup and its inverses provides the finite compressor list required
by all-trace normalization.

Let `sigma:W->U(M)` be any tracial matrix-ultraproduct homomorphism.
Write `D=sigma(Gamma)' cap M`. Normalization applied to `sigma|G` says
`sigma(G)` normalizes D. The root lamp belongs to D, so every lamp
`sigma(e_(g Gamma))` belongs to D. Therefore for every gamma in Gamma,

```
sigma(e_(gamma g Gamma))=sigma(e_(g Gamma)).
```

Conjugating these identities by h in G shows that the pair
`e_(y Gamma) e_(y c Gamma)` is killed whenever `c=g^-1 gamma g`.
Telescoping over products of such conjugates gives the same identity for
every c in `N=<<Gamma>>_G`. Every finitely supported fibre-even
configuration is a product of these two-lamp pairs. Hence
`K <= Rad_hyp(W)` with no trace-faithfulness or injectivity assumption.

The exact fibre-parity prerequisite identifies `Rad_sof(W)=K` and
`W/K=W_N`, and proves W_N residually finite. Its residual-finiteness
step is independently verified in the artifact: G has separating finite
Laurent exponent reductions, while a finite quotient of SL_d(Z) can
separate all points in any given finite nonzero lamp support. Summing
lamps over that finite quotient detects the configuration. Equivalently,
`W_N` embeds in `(C_2 wr SL_d(Z)) x G`, a residually finite group.

For any w outside K, a finite quotient of W_N detects its image; composing
with W->W_N gives a finite quotient of W detecting w. Since finite groups
are both sofic and hyperlinear, the general containments give

```
K <= Rad_hyp(W) <= Rad_sof(W) <= Res_fin(W) <= K.
```

This proves all equalities and the stated universal factorization.

## Attribution

The group data and compression argument come from Gabor Kun and Andreas
Thom, [Theorem E and Section 5](https://arxiv.org/pdf/2608.06222v3).
The analytic input is Jihao Liu,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorem 1.2/6.7, through Andreas Thom's
[conditional normalization Theorem 1.2](https://andreasthom.github.io/pdf/nonhyperlinear.pdf)
or Liu's credited Theorem 1.3/7.4. The new step here is the exact
hyperlinear-kernel conclusion from that normalization and the existing
fibre-parity computation, not a new proof of the upstream analytic input.
