---
rg: 2
id: bengi-wise-groups-are-left-orderable
kind: claim
title: The Bengi--Wise doubles are left-orderable, so they satisfy Kaplansky over every field and contain no Promislow subgroup
distinct_from:
  kaplansky-zero-divisor-conjecture: that is the conjecture; this removes the Bengi--Wise groups from the list of candidate hosts.
  zero-divisor-support-subgroup-host-constraints: that lists properties every host must violate; this shows that one literature candidate violates none of them, since it is left-orderable.
  doubles-of-left-orderable-groups-are-left-orderable: that is the general permanence lemma; this applies it to a specific construction and records which step of the source fails.
artifacts:
  - research/artifacts/bengi-wise-doubles-left-orderable-2026-09-16.md
---

N. Bengi and D. T. Wise, *Residually finite groups that do not virtually have
the unique product property*, arXiv:2602.11819v1. The TeX source (`main.tex`,
md5 `59cd378f4c0c341697af4015834a326c`) was read on 2026-09-16.

**The groups.** Let `F` be free on `a, b` (source l. 353). The source forms
two doubles in the sense of its definition (l. 184--186), namely amalgams of a
group with its copy `g -> \underline g` along a subgroup:
- `G = F *_{\widehat H} \underline F` (l. 452);
- `D(n) = G *_{\widehat Y} \underline G` (l. 481--482), with
  `\widehat Y = C_G(z)` and `z = b^{-n_0} \underline b^{n_0}`.

**Claim.** For every sequence `n` and every choice of the subgroups
`\widehat H <= F` and `\widehat Y <= G`, the groups `G` and `D(n)` are
left-orderable. Hence:
1. `D(n)` is torsion-free and has unique products;
2. `k[D(n)]` has no zero divisors, for every field `k`;
3. `D(n)` contains no subgroup isomorphic to Promislow's group `P`, and
   neither does any of its finite-index subgroups.

**Consequence for the source.** The main theorem of arXiv:2602.11819v1
(l. 503--508) states that `D(n)` "persistently contains `P`", that is, that
every finite-index subgroup contains a copy of `P`. It is false for every `n`.
The failing step is l. 191 and l. 499, which identify `P` with the double of
the Klein bottle group `K` along its torus `T`.
- The source embeds `K_i *_{T_i} \underline K_i` as `P_i = <K_i, \underline K_i>`
  (l. 496--499). The source takes `K_i ≅ K` (l. 455--457) and
  `T_i = \widehat Y ∩ K_i` (l. 468--478), and the gluing is the copy map. A
  computation in `K` gives `T_i = T`. So `P_i` is the honest double
  `K *_T \underline K`, which is isomorphic to `Z^2 x|_{-I} Z` and has
  `H_1 = Z ⊕ (Z/2)^2`.
- `P` is instead a swap-twisted amalgam of two copies of `K` over `T`, which
  glues the center of one factor to a non-central element of the other. It
  has `H_1 = (Z/4)^2`.

The introduction's theorem (l. 156--157) is therefore not established by this
paper. This claim does not decide whether some other finitely generated,
residually finite, torsion-free group persistently contains `P`.
