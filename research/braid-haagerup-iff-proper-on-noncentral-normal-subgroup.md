---
rg: 2
id: braid-haagerup-iff-proper-on-noncentral-normal-subgroup
kind: claim
title: For n >= 3, B_n has the Haagerup property iff some cnd function on P_n is proper on one non-central normal subgroup
distinct_from:
  braid-haagerup-induction-reduces-to-brunnian-braids: that claim assumes the property for B_{n-1} and uses only N = Brun_n; this needs no induction hypothesis, and it shows that properness on any non-central normal subgroup already forces properness on all of P_n modulo the center
---

Let `n ≥ 3` and let `N ⊴ P_n` be any normal subgroup with `N ⊄ Z(P_n) = ⟨Δ²⟩`. Examples are `Brun_n`,
`[Brun_n, Brun_n]`, the normal closure of one pseudo-Anosov braid, and `ker d_n ≅ F_{n−1}`. Then:

`B_n` has the Haagerup property ⟺ `P_n` admits a conditionally negative definite function whose restriction to
`N` is proper.

More precisely, if `ψ` is cnd on `P_n` and `ψ|_N` is proper, then every sublevel set `{ψ ≤ R}` lies in finitely
many cosets of `Z(P_n)`, so `ψ + e²` is proper on `P_n`, where `e: P_n → Z` is the exponent sum.

**Consequence: an obstruction to a whole class of constructions.** Suppose a cnd function `ψ` on `P_4` is bounded
on some subset that meets infinitely many cosets of `Z(P_4)`. Then `ψ` is not proper on `Brun_4`, and not on any
other non-central normal subgroup. Such subsets include:

- a Dehn twist subgroup `⟨T_c⟩`, where the image of `T_c` is elliptic with bounded orbits;
- a joint kernel `∩ ker ρ_j` that is not central.

This kills three constructions at the same step:

- finite sums of pulled-back functions whose joint kernel is non-central;
- weighted families of complex-hyperbolic monodromy distances that stay bounded along some twist subgroup (§4 of
  `research/artifacts/zp-braid-haagerup-b4-attacks-2026-09-13-part3.md`);
- any Brunnian-only construction that is not proper on the whole group.

Theorem F (`braid-haagerup-induction-reduces-to-brunnian-braids`) is therefore no easier than the original
question. Properness on `Brun_4` is not a weaker target than properness on `P_4/Z`.

Proof: `braid-haagerup-iff-proper-on-noncentral-normal-subgroup-proof`.
