---
rg: 2
id: hyperbolic-triangle-colimit-with-persistent-edge-twist
kind: claim
title: A hyperbolic triangle colimit whose moment space survives every finite cover
distinct_from:
  persistent-degree-two-class-on-hyperbolic-group: that asks for any persistent class on a residually finite hyperbolic group; this asks for the explicit edge-twist classes of a triangle colimit, certified through the moment spaces of edge-twist-extensions-of-triangle-colimits-moment-test, and assumes no residual finiteness
  hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free: that asks for torsion invisible in every finite quotient; this asks for a degree-two class on a triangle colimit that never dies in a finite cover, which kills residual finiteness of a central extension even when the colimit itself is virtually torsion-free
---

Exhibit a hyperbolic, virtually torsion-free colimit `Λ` of a triangle of finite groups
with trivial face group, and a prime `p`, such that the moment space `I_∞ <= F_p^3` of
`edge-twist-extensions-of-triangle-colimits-moment-test` is nonzero. Equivalently, some
2-cycle moment `c_12 μ_12 + c_23 μ_23 - c_13 μ_13` is nonzero on the 2-cycles of every
finite torsion-free normal cover. By (M6) of that node, some hyperbolic group is then not
residually finite.

**OPEN.**

## Attempts

- **Only `p`-covers can kill a moment** (M5). Transfer shows that covers of index prime
  to `p` do not change `I_N`. A persistence proof must therefore control the pro-`p`
  part of the finite-index subgroup lattice of one torsion-free `N`.
- **Where persistent classes must live.** The class must lie outside the image of
  continuous cohomology of the profinite completion
  (`finite-central-extension-rf-iff-virtually-splits`). So `N` must fail degree-2
  goodness at this class, and every hyperbolic virtually special group is good
  (`every-hyperbolic-group-is-good`, Attempts). Candidates therefore need (T) or some
  other obstruction to cubulation.
- **Cup products die.** If on some `N` the twist class is a cup product `h ∪ φ`, or a
  Bockstein `β(h)`, with `h in H^1(N;F_p)`, then pulling back to the `p`-cover defined by
  `h` kills it. This is the standard vanishing mechanism, recorded here as a heuristic:
  the Gysin-sequence argument was not written out. A persistent moment needs `N` whose
  classes in `H^2(N;F_p)` reached by twists are not profinitely visible, which is
  consistent with `H^1(N';F_p) = 0` along many covers.
- **Computation.** The test for one `N` is linear algebra of size `|Q| × 3|Q|/p` over
  `F_p`. Natural first inputs are the small Caprace–Conder–Kaluba–Witzel triangle groups
  with known finite quotients (`PSL_2(q)`, `PSp_6(p)`, `PSL_3(F_q)`), with `p` the order
  of the edge groups. Not yet run.
