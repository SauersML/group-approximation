---
rg: 2
id: good-cocompact-proper-groups-are-virtually-torsion-free-proof
kind: route
title: Profinite classes vanish on invisible torsion, Chern–Quillen classes do not
target: good-cocompact-proper-groups-are-virtually-torsion-free
requires:
  - chern-quillen-class-detects-all-prime-order-torsion
  - vtf-iff-chern-quillen-class-dies-on-finite-index
  - good-groups-have-no-persistent-finite-cohomology
  - universal-hyperbolic-vtf-iff-rf
  - hyperbolic-rips-complex-models-proper-actions
artifacts:
  - research/artifacts/hyperbolic-vtf-chern-quillen-persistence-2026-09-12.md
---

Full proof: artifact §4.

**(G).** In a good group every positive-degree class with finite coefficients dies
on some finite-index subgroup (`good-groups-have-no-persistent-finite-cohomology`).
In particular every Chern–Quillen class does, which is condition (3) of
`vtf-iff-chern-quillen-class-dies-on-finite-index`. So `G` is virtually
torsion-free.

**(G').** Suppose `x in R_f(G)` has order `p`, and put `P = <x>`. Let `c` be a
Chern–Quillen class at `p`, of degree `N`. Choose `k` with `q = N p^k` in the
surjective range. `H^q(G_hat;F_p)` is the colimit of `H^q(G/U;F_p)` over the finite
quotients, so `c^(p^k) = phi^* e` for some finite quotient `phi : G -> F` and some
`e in H^q(F;F_p)`. Then `res^G_P c^(p^k) = (phi|_P)^* e`. But `phi|_P` is trivial
because `x in R_f(G)`, so this restriction factors through `H^q(1;F_p) = 0`. That
contradicts `chern-quillen-class-detects-all-prime-order-torsion`. So `R_f(G)` has no
element of prime order. By the torsion-carrier criterion, which is the (2 => 1) step
of `vtf-iff-chern-quillen-class-dies-on-finite-index`, `G` is virtually torsion-free.

**(H).** Word-hyperbolic groups satisfy the hypotheses by
`hyperbolic-rips-complex-models-proper-actions`. (G') then makes every hyperbolic
group virtually torsion-free, and Wise's Proposition 9.2
(`universal-hyperbolic-vtf-iff-rf`) makes every hyperbolic group residually finite.

**Contrapositive.** If some hyperbolic group is not residually finite, then some
hyperbolic group `Q` is not virtually torsion-free
(`hyperbolic-rf-question-equals-vtf-question`). By (G'), for some prime `p`,
inflation into `H^q(Q;F_p)` fails to be surjective for infinitely many `q`. The proof
of (G') shows that the powers `c^(p^k)` of a Chern–Quillen class are not inflated.
