---
rg: 2
id: dv-s-arithmetic-hs-stable-nonhyperlinear-extension
kind: claim
title: A Hilbert-Schmidt stable S-arithmetic lattice of the right type has a non-hyperlinear finite central extension
artifacts:
  - research/artifacts/two-paper-ingestion-2026-08-19.md
distinct_from:
  hs-stability-forces-nonhyperlinear-central-extension: that is the abstract mechanism, hypothesised on (T;FD) and an abstract central extension; this is the arithmetic instance that verifies those hypotheses for S-arithmetic lattices and is what applies to SL_2(Z[1/p]).
---

**Established by citation.**  Dogon--Vigdorovich, arXiv:2506.20843v2,
Theorem 1.5 (`thm:main_S_arith` in the source):

> Let `F` be a totally real number field, `S` a finite set of valuations on `F`
> including all Archimedean ones, and `O_S` the ring of `S`-integers in `F`.
> Let `G` be a connected, absolutely almost simple, absolutely simply connected
> algebraic group defined over `F`.  Assume the `F`-rank of `G` is at least 1,
> the `S`-rank of `G` is at least 2, and that for one Archimedean valuation
> `v_0 in S` the Lie group `G(K_(v_0))` has infinite cyclic fundamental group,
> where `K_(v_0) = R`.  Let `Gamma <= prod_(v in S) G(K_v)` be a lattice
> commensurable to `G(O_S)`.  If `Gamma` is Hilbert--Schmidt stable, then
> `Gamma` has a non-hyperlinear finite central extension.

The infinite cyclic fundamental group is what supplies the central `Z`
extension required by `hs-stability-forces-nonhyperlinear-central-extension`;
the `S`-rank at least two supplies property (T;FD) via Lubotzky--Zimmer.

**The instance that matters here.**  `SL_2(Z[1/p])` is an `S`-arithmetic
lattice in `SL_2(R) x SL_2(Q_p)` satisfying these hypotheses, and by
Serre's tree decomposition it is the amalgamated free product
`SL_2(Z) *_B SL_2(Z)` over an Iwahori subgroup `B` of index three.  So the
target of the whole lane is an amalgam of virtually free groups over a finite
index subgroup -- the source calls this "surprisingly simple", and it is the
reason the `iwahori-*` lane is stated in terms of two modular vertex
representations glued along `B`.
