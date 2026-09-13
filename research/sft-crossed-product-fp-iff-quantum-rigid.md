---
rg: 2
id: sft-crossed-product-fp-iff-quantum-rigid
kind: claim
title: The crossed-product algebra of a Z^2 subshift of finite type is finitely presented exactly when the shift is quantum rigid
distinct_from:
  minimal-subshift-crossed-product-is-not-finitely-presented: that kills finite presentation for minimal Z-subshifts through LEF; this characterizes finite presentation for Z^2 SFTs, where LEF is unavailable, by a noncommutative local-to-global property.
  sfts-without-finite-orbits-are-not-residually-finite-actions: that is a classical statement about finite models of an SFT action; this is about operator-valued local tilings, which need no finite orbit.
artifacts:
  - research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `k` be a field and `Ω ⊆ A^(Z^2)` an SFT with forbidden patterns
in `B_r`. Put `R_Ω = LC(Ω, k) ⋊ Z^2`.

Call `Ω` *`D`-quantum rigid* if the following holds for every `k`-vector space `W` and every family
of idempotents `E_a(z) ∈ End_k(W)`, with `a ∈ A` and `z ∈ Z^2`, such that:
- (Q1) for each `z`, the `E_a(z)` form a partition of unity into orthogonal idempotents;
- (Q2) `E_a(z)` and `E_b(z')` commute whenever `|z - z'| <= 2D`;
- (Q3) for every `z`, the product over `h ∈ B_D` of `E_(pi(h))(z + h)` vanishes for every pattern
  `pi` on `B_D` that does not occur in `Ω`.

The conclusion required is that all the `E_a(z)` commute.

**Theorem.** `R_Ω` is finitely presented as a `k`-algebra iff `Ω` is `D`-quantum rigid for some
`D >= r`.

The hypothesis is local. There is no translation invariance, no dimension bound, and no finiteness
of `W`.

**Certificates.** Two configurations that agree on a wall of width `> 2D` and differ on both sides
refute `D`-rigidity, with `W = k^2`.

**Calibration.**
- Positive entropy produces such walls at every scale
  (`positive-entropy-sft-crossed-products-are-not-fp`).
- Ledrappier's shift is rigid (`ledrappier-crossed-product-is-finitely-presented`).
- The theorem is the algebra analogue of the Bieri--Strebel picture for metabelian lamp groups.
  There, finite presentation also comes from propagating commutation.

**Novelty.** Not searched in the literature; a bounded check of this graph found no statement of
this kind.

Route: `sft-crossed-product-fp-iff-quantum-rigid-proof`.
