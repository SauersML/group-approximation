---
rg: 2
id: finite-scale-sofic-profiles-kill-compression-defects
kind: claim
title: A sofic representation whose Kazhdan cluster profile lives on finitely many scales normalizes the whole centralizer, so every compression-defect witness is multi-scale in every sofic representation
distinct_from:
  finite-scale-compressors-preserve-kazhdan-fixed-algebras: that is the fixed-algebra level (W1) and kills no defect; this is the centralizer level (W2), obtained by feeding its mass-transport item 3 into both calls of Kun--Thom Lemma 4.4, and it kills the whole defect D_G(L).
  ambient-decomposition-kun-thom-normalization: that needs an ambient expander decomposition of the generator graph of sigma on <L, compressors>; this needs no ambient decomposition, only a scale hypothesis on sigma|_L alone, the same for all compressors.
  bounded-period-compressors-carry-no-sofic-defect: that kills one compressor at a time under a bounded cluster period, which is a property of the compressor; this kills all compressors at once under a profile hypothesis on sigma|_L. The hypotheses are incomparable, since a single long drifting cycle of equal-size clusters is finite-scale with unbounded period.
  twisted-lef-tower-order-budget-kills-compression-defects: that is exact LEF models of the kernel K twisted by phi, with a Lagrange count; this is Hamming sofic representations of the whole group G, with a mass-transport count and Kun--Thom's index-less-than-2 step.
  kun-thom-sofic-centralizer-normalization: that assumes property (T) of the ambient group; this assumes nothing about the ambient group beyond soficity.
  sofic-groups-kill-rigid-compression-defects: that kills the defect when the compressor group is Kazhdan; here the compressor group is arbitrary.
artifacts:
  - research/artifacts/kun-thom-2608-06222-section4-finite-scale-excerpts.md
  - research/artifacts/kun-thom-2608-06222-section4-ambient-audit.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

**ESTABLISHED.** The derivation is route
`finite-scale-sofic-profiles-kill-compression-defects-proof`. Its trust surface is the
Kun--Thom Section 4 proof import already accepted by
`ambient-decomposition-kun-thom-normalization-audit`, plus the ESTABLISHED
`finite-scale-compressors-preserve-kazhdan-fixed-algebras`.

## Setting

- `L` is a Kazhdan group with finite symmetric generating set `S`, and `L <= G` for a
  countable group `G`.
- `U` is a nonprincipal ultrafilter on `N`, and `sigma : G -> S_U = prod_U Sym(Y_n)` is a
  sofic representation, meaning `tr sigma(g) = 0` for `g != 1`, with lifts `sigma_n(g)`.
- `Q_n = {Q_(n,i) : i in I_n^0}` is a cluster frame of `sigma|_L`, as in
  `bounded-cluster-period-preserves-kazhdan-fixed-algebras`. These are the components of
  Kun's edited expander decomposition, which Kun--Thom Section 4 also uses.
- An **admissible groupoid choice** is a choice of the data of Kun--Thom Lemma 4.2
  (artifact K1): scales `eps_n, q_n, r_n -> 0`, retained clusters `I_n`, and the finite
  cluster groupoid `C_n => I_n` of allowed partial bijections. From it, put
  - `o_n(i) = |Orb_(C_n)(i)|`;
  - `k_n(i) = |C_n(i,i)|`;
  - `o_n = k_n = 1` on clusters outside `I_n`.

For functions `psi_n : Y_n -> R`, let `(FS)` be the condition used for the log-size in the
fixed-algebra node. For every `eps > 0` there are `k` and `Lambda` such that, for
`U`-almost every `n`, some union of `k` intervals of length `<= Lambda` carries at least
`1 - eps` of the uniform mass of `psi_n`.

**Definition.** `sigma|_L` is **finite-scale** if both of the following hold.
- **(FS-size)** `phi_n(y) = log |Q_n(y)|` satisfies `(FS)`.
- **(FS-groupoid)** For every finite family of sequences tending to `0` along `U`, there is
  an admissible groupoid choice for which those sequences are `o_U(eps_n)`, and for which
  `log o_n(Q_n(y))` and `log k_n(Q_n(y))` both satisfy `(FS)`.

These are conditions on `sigma|_L` only. Nothing is assumed about any compressor.

## Statement

Put `C = C_(S_U)(sigma(L))`, and use the defect `D_G(L)` of
`compression-defect-dies-in-finite-dimensions`.

1. **(FSK1: centralizer normalization.)** If `sigma|_L` is finite-scale, then
   `sigma(s) C sigma(s)^-1 = C` for every `s in Comp_G(L)`. So `sigma(<Comp_G(L)>)`
   normalizes `C`.
2. **(FSK2: the defect dies.)** If `G` has one sofic representation `sigma` with `sigma|_L`
   finite-scale, then `D_G(L) = 1`.
3. **(FSK3: consequence for (EK1).)** Let `(K, phi, L)` be a witness for
   `torsion-free-sofic-extrinsic-kazhdan-defect-kernel`, so `D_G(L) = K x {0} != 1`. Then for
   every nonprincipal `U` and every sofic representation `sigma` of `G = K semidirect Z`,
   `sigma|_L` is not finite-scale. So either the log cluster sizes spread over unboundedly
   many scales, or some prescribed errors force every slow enough admissible groupoid to
   have a multi-scale orbit or isotropy profile.

## What this kills

**Class.** Sofic witnesses to a nontrivial compression defect `D_G(L)` of a Kazhdan `L`
that have a single sofic representation in which the `L`-clusters, their groupoid orbits
and their isotropy groups each live on finitely many scales. This covers both W1
(fixed-algebra growth) and W2 (centralizer drift) of Attempt 21 on the (EK1) node. The
compressors can be arbitrary: wild, of unbounded period, with a non-Kazhdan compressor
group. No ambient expander decomposition is used.

**Invariant.** The three log-profiles of `sigma|_L`: cluster size, groupoid orbit size and
isotropy order.

**Where every member dies.** Kun--Thom's index step (artifact K6). The functor attached to
a compressor gives an injection of isotropy groups whose index is
`k_n(i)/k_n(pi(i))`. Mass transport of `log k_n` along the permutation `sigma_n(s)` forces
this ratio below `2` on almost all cluster weight, because the profile is finite-scale. So
the index is `1`, and a centralizer element conjugated by `sigma(s)` is again a patched
bisection of the groupoid.

**Survivors.** A witness must make **every** sofic representation multi-scale on `L`. That
means a doubling-tower pattern, as in item 4 of the fixed-algebra node, in cluster size,
orbit size or isotropy order, with compressors carrying mass across unboundedly many
scales.

## Open reduction

Refuting (EK1) would follow from the following statement.

**(PR) Profile regularization.** Every sofic group `G` containing a Kazhdan `L` has a sofic
representation with `sigma|_L` finite-scale.

(PR) is **not** claimed here. It holds when some sofic representation of `G` has a
finite-scale profile. It is exactly as hard as producing a witness whose sofic
representations are all towers. The direct-sum and tensor constructions of sofic
representations do not obviously regularize the profile. A direct sum over scales is not
`G`-invariant, because compressors move mass between scales. Tensoring with a second
representation multiplies cluster sizes, so the log-sizes add and the spread survives.
