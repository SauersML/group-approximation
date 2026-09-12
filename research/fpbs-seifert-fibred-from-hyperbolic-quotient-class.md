---
rg: 2
id: fpbs-seifert-fibred-from-hyperbolic-quotient-class
kind: route
title: A Seifert-fibred group with hyperbolic base is an extension of a Fuchsian group by the fibre
target: fpbs-seifert-fibred-every-generating-set
requires:
  - fpbs-hyperbolic-quotient-every-generating-set
---

Let `M` be a closed Seifert-fibred 3-manifold with hyperbolic base orbifold
`B`. The regular fibre generates an infinite cyclic normal subgroup of
`pi_1(M)` with quotient `pi_1^orb(B)`. That quotient is a cocompact Fuchsian
group, hence non-elementary word hyperbolic. So `pi_1(M)` lies in the class of
`fpbs-hyperbolic-quotient-every-generating-set`, and the premise gives `p_c < p_u`
on each of its Cayley graphs.

This route is independent of `fpbs-seifert-fibred-from-amenable-wq-normal-class`.
That route goes through relative susceptibility; this one goes through the two
fibre estimates on the Fuchsian quotient.
