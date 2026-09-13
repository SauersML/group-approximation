---
rg: 2
id: purely-infinite-simple-projective-el-groups-stable-nonsofic
kind: claim
title: Over a finite field, simple quotients of EL_N over purely infinite simple algebras are nonsofic and permutation stable, the mirror of the unstable Pestov group
distinct_from:
  purely-infinite-simple-algebras-have-nonsofic-el-groups: that is nonsoficity of EL_n itself; this adds the projective quotient and the permutation stability of the simple quotients.
  binary-leavitt-unit-group-is-permutation-stable: that is stability of one group via its character simplex; this is stability for every simple quotient EL_N/Z over a purely infinite simple algebra, from simplicity alone.
artifacts:
  - research/artifacts/un-stability-nonsofic-2026-09-13-part1.md
---

**ESTABLISHED.** Let `k` be a finite field, `R` a countable purely infinite simple unital `k`-algebra
(Ara–Goodearl–Pardo sense), `N >= 2`, `Z = Z(EL_N(R))`.

1. **Nonsofic.** If `Z ⊆ k^x · 1`, then `S_N = EL_N(R)/Z` is nonsofic.
2. **Stable.** If moreover `S_N` is simple, then `S_N` is permutation stable, strictly and flexibly, with only
   trivial correcting homomorphisms, and it is not residually finite.

Proof: `purely-infinite-simple-projective-elementary-groups-proof`.

**Instances.** Take `R = A_k(𝒢)` for a minimal effective Hausdorff ample groupoid `𝒢` with compact infinite
unit space, purely infinite simple, and `N >= 3`.
- By `steinberg-elementary-groups-are-simple-mod-centre` (reviewed PASS), `Z ⊆ k^x · 1` and `S_N` is simple.
  If `R` is finitely generated, `S_N` has property (T).
- This includes the Leavitt algebras `L_k(1,d)`, `d >= 2`: Cuntz groupoids, purely infinite simple by AGP
  Theorem 4.2 as recorded in `purely-infinite-simple-algebras-have-nonsofic-el-groups`.
- So each `EL_N(L_k(1,d))/Z`, `N >= 3`, is an infinite, finitely generated, simple Kazhdan group that is
  nonsofic and permutation stable.

**The stability face of the dichotomy.** For simple Kazhdan groups `S = EL_N(A_k(𝒢))/Z` over finite fields,
by `infinite-simple-group-permutation-stable-iff-nonsofic`:
- **measure with towers** (matricial algebras, e.g. Pestov's `LC(X,F_q) ⋊ Z`): `S` is LEF, sofic and unstable;
- **purely infinite** (halvable corner): `S` is nonsofic and stable;
- **middle** (neither): stability of `S` is the same open question as its soficity.
