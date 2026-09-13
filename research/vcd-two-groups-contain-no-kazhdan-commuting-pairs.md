---
rg: 2
id: vcd-two-groups-contain-no-kazhdan-commuting-pairs
kind: claim
title: In a group of virtual cohomological dimension two, commuting partners of infinite subgroups are virtually free, so compression and lamp certificates have no instance
distinct_from:
  titz-witzel-kernel-not-elementary-sofic: that excludes the positive certificates (the elementary sofic closure) for the Titz--Witzel kernels; this excludes the negative certificates built from commuting compressed Kazhdan pairs or from infinite lamp groups, for every group of virtual cohomological dimension at most two.
  openai-expander-matching-criterion: that is the nonsoficity criterion; this proves that inside a group of virtual cohomological dimension at most two its hypotheses force the commuting factor to be finite, so the criterion never fires there.
  nonsofic-subgroups-of-radu-lattice-have-nonamenable-edge-groups: that filters nonsofic subgroups of Radu's lattice through its two tree actions; this is a dimension count that holds in every group of virtual cohomological dimension at most two and uses no splitting.
---

**ESTABLISHED.** Let `G` be a group with a finite-index subgroup `G_0` such that
`cd_Z(G_0) <= 2`.

```text
(CD1) If A, B <= G commute, A cap B = 1 and A is infinite, then B is virtually free.
(CD2) If in addition A has property (T), then B is finite.
(CD3) G contains no copy of Z^3, and every finite subgroup of G has order at most [G:G_0].
      So no generalized wreath product L wr_X H = (directSum_X L) semidirect H with
      L != 1 and X infinite embeds in G.
```

A finitely generated virtually free group is residually finite, hence LEF. So in (CD1) every
finitely generated commuting partner `B` of an infinite subgroup is LEF.

## Instances

- The five Titz Mite--Witzel lattices `Gamma_i^q` and their simple finite residuals
  `Gamma^_i^q`. They act freely and cocompactly on contractible two-dimensional buildings
  (`titz-witzel-simple-kazhdan-cat0-lattices-exist`), so `cd = 2`. The same holds for the
  involutory index-two overgroup `barGamma_1^2` of `K = Gamma_1^2`.
- Radu's BMW lattice `Gamma_R`, whose index-four subgroup `pi_1(S_R)` acts freely on
  `T_3 x T_3` (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`).
- Every virtually torsion-free group acting properly on a contractible two-dimensional
  complex.

## What it excludes

1. **The expander-matching criterion** (`openai-expander-matching-criterion`, both versions)
   and its formalized twin `one-sided-compression-nonsofic-criterion`. Their hypotheses give a
   subgroup `J` that commutes with an infinite Kazhdan subgroup (`Gamma`, or its compressed copy
   `q Gamma q^-1`) and meets it trivially. By (CD2), `J` is finite, hence LEF. So the criterion
   proves no subgroup of `G` nonsofic.
2. **Kun--Thom generalized wreath products** (`kun-thom-nonsofic-wreath`). An infranormal
   subgroup that is not normal has infinite index: if `[G:Gamma] < infinity` and
   `t Gamma t^-1 <= Gamma`, the two subgroups have the same index, so they are equal. Then the
   compression semigroup is the normalizer, and it generates `G` only if `Gamma` is normal. So
   `(Z/2) wr_(G/Gamma) G` has an infinite lamp set and does not embed, by (CD3). The same holds
   for lamps from any nontrivial group.
3. **Wreath shifts inside compression groups.** The torsion-free Fournier--Facio group contains
   `S wr Z`, where `S` is its infinite torsion-free simple factor
   (`fournier-facio-group-contains-simple-wreath-shift`). The base `S^(Z)` contains `Z^3`, so
   this configuration does not embed either.

**Not excluded.**
- The Kun--Thom double `G *_Gamma G` (`kt-pair-group-double-is-nonsofic`): this dimension count
  says nothing about amalgams.
- Certificates of a different shape: a strict cellular automaton
  (`radu-bmw-lattice-nonsurjunctive`), a one-sided inverse over the group algebra
  (`radu-bmw-lattice-group-algebra-not-stably-finite`), or the sparse-defect repair inequality of
  `titz-witzel-soficity-is-one-finite-csp`.

## What separates Khanh's group from the Titz--Witzel kernels

The known finitely presented simple Kazhdan groups divide as follows.

- **Khanh's group.** `L_(F_2)(1,2)^x` is finitely presented, simple, Kazhdan and nonsofic
  (`fp-simple-nonsofic-group`). Its nonsoficity certificate is a configuration that (CD2)
  forbids in dimension two: the nine-leaf configuration
  (`openai-nine-leaf-leavitt-configuration`) puts a compressed infinite Kazhdan subgroup next to
  a commuting non-LEF subgroup. The group also contains Thompson's `V`, so it
  has finite subgroups of unbounded order and infinite `vcd`.
- **The Titz Mite--Witzel residuals.** They have `cd = 2`. By (CD2) an infinite Kazhdan
  subgroup commutes with no nontrivial subgroup that meets it trivially.

So "no commuting Kazhdan pair" is not an accident of the known search: it is forced by
dimension. A proof that `K` is nonsofic (`titz-witzel-kernel-nonsofic`) must use a mechanism
other than compression with a commuting factor and other than lamps. Conversely, the only
published mechanism that makes a finitely presented simple Kazhdan group nonsofic cannot be the
reason these groups fail to be sofic, if they do.

Credit: the three standard inputs are Swan's theorem (cd one implies free), the
Lyndon--Hochschild--Serre spectral sequence, and the fact that Kazhdan groups have finite
abelianization. The observation that they fence off these certificates is new here. Proof:
`vcd-two-groups-contain-no-kazhdan-commuting-pairs-proof`.
