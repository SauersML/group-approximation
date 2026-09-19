---
rg: 2
id: binary-leavitt-single-root-character-orbit-has-zero-gap
kind: claim
title: The single-root Leavitt character orbit is infinite but has zero finite-set Schreier gap
distinct_from:
  surviving-leavitt-corona-character-has-infinite-parabolic-orbit: that proves infinitude of the orbit under one root subgroup; this computes the same orbit as a locally finite translation action and proves that no finite subset of that subgroup expands it.
  one-seed-infinite-character-expansion-collapses-mark: that turns a uniform Schreier gap into character-sector collapse; this proves that the one-root orbit used in the Leavitt infinitude argument cannot supply that prerequisite.
  affine-leavitt-active-root-character-orbits-are-aperiodic: that uses the full odd-characteristic affine Steinberg actor and an external uniform spectral gap; this concerns the intrinsic characteristic-two single-root translation orbit and proves its gap is zero.
artifacts:
  - research/binary-leavitt-single-root-orbit-zero-gap-proof.md
---

**ESTABLISHED ORBIT-GAP FENCE.**  In the notation of
`surviving-leavitt-corona-character-has-infinite-parabolic-orbit`, choose a
nontrivial coordinate character `chi_i` and `j!=i`.  The orbit of `chi`
under the single upper-left root subgroup

```text
U_ij={x_ij(r):r in L_(F_2)(1,2)}
```

is the regular translation action of the additive quotient

```text
L/K,       K={r:chi_i(ra)=1 for every a in L}.                (SRG1)
```

The quotient is infinite, but it is an elementary abelian `2`-group.  For
every finite symmetric subset `S subset U_ij`, the normalized Schreier
operator on this orbit has norm exactly one.  Equivalently, its spectral gap
is zero.

Thus the one-root proof of orbit infinitude cannot be fed into
`one-seed-infinite-character-expansion-collapses-mark`.  Any expansion-based
Property-`(T)`-free attack must add finitely many actors outside this root
subgroup and prove a genuinely new uniform gap for their joint action.  The
infinite orbit itself contributes no expansion: every finite root-actor menu
breaks it into finite translation components.

No Property `(T)`, approximation theorem, or literature input is used.

DERIVATION
binary-leavitt-single-root-orbit-zero-gap-proof
