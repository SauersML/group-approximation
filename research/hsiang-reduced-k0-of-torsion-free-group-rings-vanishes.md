---
rg: 2
id: hsiang-reduced-k0-of-torsion-free-group-rings-vanishes
kind: claim
title: "Hsiang's conjecture: the reduced projective class group of Z[G] vanishes for every torsion-free group G"
distinct_from:
  cohen-lyndon-torsion-free-k0-base-ring-conjecture: that is the established case of torsion-free Cohen--Lyndon groups over regular coefficient rings; this is the open statement for every torsion-free group with integer coefficients.
  f-infinity-groups-of-finite-cd-are-of-type-f: that asks only that the Wall class of each finitely presented group of type FP vanish; this asks that the whole reduced projective class group vanish for every torsion-free group.
  f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f: that is the established per-group implication from vanishing reduced K_0 to type F; this is the open vanishing statement itself, for all torsion-free groups.
---

For every torsion-free group `G`, `K̃_0(Z[G]) = 0`. Equivalently, every
finitely generated projective `Z[G]`-module is stably free.

Ferry–Ranicki, arXiv:math/0008070, Section 2 (TeX source read on MSI,
2026-09-13): "At present, no example is known of a torsion-free infinite
group π with K̃_0(Z[π]) ≠ 0. Indeed, Hsiang has conjectured that
K̃_0(Z[π]) = 0 for any torsion-free group π. (See Farrell and Jones [FJ],
pp. 9--11)."

This is the `K̃_0` part of Conjecture 1.3 of W. Lück and H. Reich,
arXiv:math/0402405, as quoted in
[[f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f]]. By their text,
the K-theoretic Farrell–Jones conjecture implies it.

It answers Zaremsky's Problem 1.21 positively through
[[f-infinity-finite-cd-groups-type-f-via-hsiang]].

## Attempts

- **Farrell–Jones.** The conjecture holds for every torsion-free group
  satisfying the K-theoretic Farrell–Jones conjecture, so it is known for the
  classes listed in
  [[f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f]]. The global
  statement is open. For torsion-free groups, the full coefficient-rich
  conjecture is equivalent to one assertion about a single group:
  [[full-farrell-jones-fixed-fp-torsion-free-tester]].
- **One group.** By [[hsiang-reduced-k0-via-universal-tester]] and
  [[universal-tester-reduced-k0-from-hsiang]], this claim is equivalent to
  `K̃_0(Z[U]) = 0` for the fixed finitely presented torsion-free group `U` of
  [[higher-whitehead-universal-finitely-presented-torsion-free-group]]; see
  [[reduced-k0-of-universal-fp-torsion-free-tester-vanishes]]. The reduction
  is exact, but it computes nothing yet.
