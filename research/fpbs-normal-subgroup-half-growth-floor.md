---
rg: 2
id: fpbs-normal-subgroup-half-growth-floor
kind: claim
title: A normal subgroup grows at least at half the volume rate divided by the growth of any centralizer in it, so half-growth two-point certificates cannot see normal subgroups with a cyclic undistorted centralizer
distinct_from:
  fpbs-pointwise-critical-growth-decay-fails: that refutes the pointwise bound tau_(p_c)(o,x) <= gr^(-(1-eps)|x|) on products of trees; this is a group-theoretic floor on the growth of a normal subgroup, and shows that even the weaker bound C gr^(-|x|/2), which that node leaves open, certifies nothing along N once N has an element with linear-growth centralizer
  fpbs-percolation-kesten-normal-gap: that is the gap conjecture; this kills one class of approaches to it (radial pointwise decay summed over N) on a named class of groups and proves nothing about the gap itself
  fpbs-sphere-two-point-rate-right-continuous-universal: that asks for right-continuity of a sphere rate at p_c; this shows that on the class below the radial route fails already at p_c, before any continuity question arises
---

**ESTABLISHED.** Let `G = Cay(Gamma,S)`, `|x|` the word length, `B_r` the ball,
and `gr = lim |B_r|^(1/r)`. Let `N` be a normal subgroup and `n0 ∈ N \ {e}`,
with centralizer `C = C_Gamma(n0)`. Then for every `r >= 0`:

```text
|N ∩ B_(2r+|n0|)|  >=  |B_r| / |C ∩ B_(2r)|  >=  gr^r / |C ∩ B_(2r)|.
```

Write `c = limsup_R |C ∩ B_R|^(1/R)`. Then:

1. **(Floor)** `liminf_R |N ∩ B_R|^(1/R) >= sqrt(gr) / c`.
2. **(Divergence)** If `gr > 1` and `|C ∩ B_R| <= A R` for all `R >= 1`, then
   `sum_(n ∈ N) gr^(-|n|/2) = infinity`.

**Class where (2) applies.** Let `Gamma` be acylindrically hyperbolic and let
`N` be an infinite normal subgroup. Then `N` contains a loxodromic WPD element
`n0` (Osin). Its centralizer is virtually cyclic, and a loxodromic element is
undistorted, so `|C ∩ B_R| = O(R)`. This class includes:

- non-elementary hyperbolic groups;
- mapping class groups;
- `Out(F_n)`;
- non-product right-angled Artin groups.

The group-theoretic inputs are standard but are not re-verified here. The
inequality itself is proved in full in
`fpbs-normal-subgroup-half-growth-floor-proof`.

**What it kills.** Call a *radial certificate* along `N` any argument that shows
`chi^N_p = sum_(n ∈ N) tau_p(o,n) < infinity` from a bound
`tau_p(o,x) <= C e^(-a|x|)` depending only on `|x|`.

- By (1), such a certificate needs `a >= (1/2) log gr - log c`.
- By (2), the half-growth rate `a = (1/2) log gr` fails exactly at `p = p_c`,
  on every normal `N` in the class above.

So the sparse-subgroup route to the gap needs two things:

- a pointwise half-growth bound `tau_(p_c)(o,x) <= gr^(-|x|/2)`, which is
  unproved; Hutchcroft's bound (arXiv:1605.05301) controls only the worst pair
  `kappa`;
- right-continuity of the decay rate above `p_c`.

Even with both, it reaches only normal subgroups in which every nontrivial
element has a centralizer of exponential growth larger than `sqrt(gr)/v_N`.
Direct and central products are examples. That is essentially the product case,
where `fpbs-tree-products-schreier-kesten-gap-iff-not-co-amenable` and
`fpbs-tree-product-thin-section-subgroups-have-tilt-gap` already give the gap
on tree products.

**What it does not kill.** Radial certificates at rates above half growth are
untouched. On regular trees `tau_(p_c)(o,x) = gr^(-|x|)`, and then the
certificate works exactly when `v_N < gr`, which by cogrowth means `Q` is
nonamenable. Mean-field heuristics predict rates near `log gr` in axis
directions. The kill is a floor for the method, not an obstruction to it.
