---
rg: 2
id: non-hyperlinear-from-internality-and-thom-double
kind: route
title: "Thom's conditional double construction turns universal internality into a nonhyperlinear group"
target: non-hyperlinear-group
requires:
  - kazhdan-commutants-are-internal
  - kun-thom-nonsofic-wreath
artifacts:
  - research/artifacts/liu-section-six-acceptance-and-thom-bypass-2026-09-20.md
---

## Attribution

The implication and double witness are Andreas Thom's
[*A conditional construction of a nonhyperlinear group and the centralizer problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
Theorems 1.2-1.3, checked through their proofs in Sections 2-5. The
explicit pair is Gabor Kun and Andreas Thom's
[Theorem E](https://arxiv.org/abs/2608.06222); their paper also supplies
the related lamp construction. The proposed universal analytic input is
Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 1.2 / 6.7. This route bypasses Liu Section 7 and
the ordinary-wreath/double equivalence, and makes no unconditional import
of Liu's analytic result.

Use the `q=2,r=d=3` pair from the second prerequisite:

```text
Gamma=EL_3(F_2[x_1,x_2,x_3]),
G=EL_3(F_2[x_1^(+-1),x_2^(+-1),x_3^(+-1)]) rtimes SL_3(Z).
```

Both groups are countable, finitely generated and Kazhdan; `Gamma` is
infranormal and nonnormal. Form the countable double `P=G *_Gamma G`.
Choose a strict compressor `t` and `h in Gamma \ t Gamma t^-1`.
Such a compressor exists because otherwise the whole compression
semigroup would normalize `Gamma`, forcing normality in its generated
group `G`.

For any homomorphism `pi:P->U(M)`, the first prerequisite supplies
internality for the subgroup and first vertex representations. Thom's
Theorem 1.2 gives normalization of `A=pi(Gamma)' cap M` by the first
vertex. Write `t_1,t_2` for the two copies of `t`. The element
`c=t_1^-1 t_2` centralizes `Gamma`, so `pi(c) in A`. Normalization by
`pi(t_1)` then puts `pi(t_2 t_1^-1)` in `A`. It commutes with `pi(h)`.

The commutator `[h,t_2 t_1^-1]` is nonidentity in `P`: its form
`(h t_2)(t_1^-1 h^-1 t_1)(t_2^-1)` is an alternating reduced word of
length three. The middle factor is outside the amalgam by the choice of
`h`, and the other factors are outside it because a strict compressor is
not an element of `Gamma`. The normal-form theorem proves nontriviality.
Its image under `pi` is nevertheless identity. Thus no such `pi` is
injective, and `P` is not hyperlinear. It witnesses the target.

The source theorem and the all-trace normalization argument used here are
verified in the attached artifact. The universal internality prerequisite
remains explicit; proving this conditional deduction does not prove it.
