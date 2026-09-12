---
rg: 2
id: kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient
kind: claim
title: Sofic approximations preserve the expander blocks of a Kazhdan kernel whose quotient admits no nontrivial sofic representation
distinct_from:
  kun-expander-decomposition-formalized: that produces the expander blocks for one Kazhdan group; this shows that the blocks of a normal Kazhdan subgroup are invariant under the whole ambient group, when the quotient has no nontrivial homomorphism into a universal sofic group.
  hyperbolic-kazhdan-cover-of-leavitt-unit-group: that records the finite-image form, where every finite image of the cover is the image of its kernel; this is the same phenomenon for arbitrary sofic approximations.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**ESTABLISHED.** Let `1 -> N -> G -> Q -> 1` be a short exact sequence of
countable groups, where:

- `N` is infinite and Kazhdan, with finite generating set `S`;
- every homomorphism from `Q` into a universal sofic group `S_U` is trivial.

Let `sigma_n : G -> Sym(X_n)` be a sofic approximation. Edit `o(|X_n|)` edges
so that the `S`-graphs of `sigma_n` are disjoint unions of blocks `B` with a
uniform Cheeger constant (`kun-expander-decomposition-formalized`). Then for
every `g in G` and every `eps > 0`,

```text
sum of |B| over the blocks B with |sigma_n(g)B symmetric-difference B| > eps|B|   =   o(|X_n|)   along U.
```

Equivalently, in Kun--Thom's notation, `D_U^(sigma(G)) = D_U^(sigma(N))`: the
fixed algebra of `N` is already fixed by `G`.

**Instance.** For the Leavitt cover
(`hyperbolic-kazhdan-cover-of-leavitt-unit-group`), `Q = R^x` is simple and
nonsofic. A nontrivial homomorphism `R^x -> S_U` would be injective, and
amplifying an injective one gives a sofic approximation. So in every sofic
approximation of that hyperbolic Kazhdan group, the ambient group preserves
the kernel's expander blocks.

Derivation: `kazhdan-kernel-block-invariance-proof`.

**What it rules out.** No block-level datum of a sofic approximation can see
the quotient. A proof of `sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`
for the cover has to separate elements outside `N` from `N` inside a single
expander block, where both act freely and ergodically.
