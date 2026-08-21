---
rg: 2
id: iwahori-eisenstein-angle
kind: claim
title: The two Iwahori restriction maps are uniformly transverse on Eisenstein cohomology
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-cuspidal-hecke-angle: that handles square-integrable classes through Deligne; this handles the boundary (Eisenstein) classes, whose Hecke eigenvalue at 2 is the degenerate value 3 and whose harmonic representatives are not square-integrable, so a separate finite computation is needed.
---

**ESTABLISHED, with an explicit constant.**  With notation as in
`iwahori-cuspidal-hecke-angle`, let `H^1_Eis` denote the Eisenstein
(boundary-residue) part of `H^1(Gamma(m),Ad rho)` for an odd congruence level
`m`.  Equip its residue model with the unweighted cusp-count norm.  For the
two Iwahori restriction maps one has

```text
||res_1 f-res_2 g||^2 >= ||f||^2+||g||^2.             (EIA1)
```

Consequently

```text
||res_1 f-res_2 g|| >= (||f||+||g||)/sqrt(2),         (EIA2)
```

uniformly in the odd level, the coefficient representation, and its
dimension.  The estimate holds on the full residue spaces, hence also after
the residue-sum-zero condition and passage to Eisenstein cohomology.  No
property `(T;FD)` input is needed for this sector.

The mechanism is the asymmetric cusp-width pair `(2,1)`.  The index-three
Iwahori cover has, over every congruence cusp, one lift of ramification index
two and one lift of index one.  Relative to the opposite modular vertex the
same two Iwahori cusp families have indices one and two.  After harmless
unitary relabelings of cusps and unitary coefficient transports, the
restriction mismatch therefore has the form

```text
(f,g) |-> (2 A f-C g, B f-2 D g),                     (EIA3)
```

where `A,B,C,D` are unitaries.  If `a=||f||` and `b=||g||`, expansion and
Cauchy--Schwarz give

```text
||2Af-Cg||^2+||Bf-2Dg||^2
 >= 5(a^2+b^2)-8ab
 = a^2+b^2+4(a-b)^2
 >= a^2+b^2.                                         (EIA4)
```

This also explains why the Eisenstein Hecke eigenvalue `3` is not a zero
mode here: the Petersson degeneracy-map identity used on cuspidal forms has
discarded the two different boundary ramification weights.  Retaining those
weights produces `(EIA3)` and the gap one.
