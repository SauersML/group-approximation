---
rg: 2
id: nonsingular-coefficient-kernel-in-locally-indicable-residual
kind: claim
title: The kernel of a nonsingular coefficient map dies in every locally indicable quotient
distinct_from:
  nonsingular-adjunction-preserves-approximation-radicals: that bounds the kernel by the MF and hyperlinear radicals through matrix approximations; this bounds it by the locally indicable residual through Howie's theorem, with no approximation input.
  howie-locally-indicable-nonsingular-equations-are-solvable: that is injectivity for locally indicable coefficient groups; this transfers it to every group through its locally indicable quotients.
artifacts:
  - research/artifacts/kl-nonamenable-shapes-2026-09-13.md
---

For a group `G`, let `Rad_LI(G)` be the intersection of the kernels of all
homomorphisms from `G` to locally indicable groups.

Let `G` be any group, `w in G * <t>` with `deg_t(w) != 0`, and
`q : G -> G_w = (G * <t>)/<<w>>` the coefficient map. Then

    ker(q)  <=  Rad_LI(G).

In particular:

1. If `G` is residually locally indicable, then `q` is injective. This holds for
   every `t`-shape.
2. Suppose a pair `(G, w)` violates the nonsingular Kervaire--Laudenbach
   conjecture. Then some `g != 1` in `ker(q)` dies in every locally indicable
   quotient of `G`, so `G` is not residually locally indicable. With
   `nonsingular-adjunction-preserves-approximation-radicals`, that `g` also lies
   in `Rad_MF(G)` and in `Rad_hyp(G)`.

The same argument works with any class of coefficient groups on which the
conjecture holds, provided the class has no shape hypothesis. That is why it is
stated for Howie's class, and not for torsion-free groups at amenable shapes:
passing to a quotient can cancel `t`-letters and change the shape.
