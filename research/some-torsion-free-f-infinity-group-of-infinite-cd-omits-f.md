---
rg: 2
id: some-torsion-free-f-infinity-group-of-infinite-cd-omits-f
kind: claim
title: Some torsion-free group of type F_infinity with infinite cohomological dimension contains no copy of Thompson's group F
artifacts:
  - research/artifacts/zp-thompson-free-infinite-dimensional-f-infinity-2026-09-13.md
---

There is a torsion-free group `G` of type F_∞ with `cd G = ∞` such that no
subgroup of `G` is isomorphic to Thompson's group `F`.

This is the affirmative answer to Zaremsky Problem 2.8
(`zaremsky-2-08-infinite-dim-torsion-free-f-infinity-without-f`).

## Attempts

- **Thompson-like groups.** Dead: they contain `F`. This covers `F_n`,
  `F_{n,r}`, the Stein groups, braided and pure braided `F`, cloning-system groups
  `T(G_*)`, Lodha–Moore, Monod's piecewise projective groups, and the
  Brin–Thompson groups.
- **Elementary amenable groups.** Dead: torsion-free elementary amenable groups of
  type FP_∞ have finite cohomological dimension (Kropholler; import pending
  verification).
- **Linear groups.** They omit `F` by the Tits alternative, but they fall under
  Kropholler's class LH𝔉, where FP_∞ forces finite cd (import pending
  verification).
  - `SL_n(Z[t])` has infinite vcd but is not FP_{n−1} (Bux–Mohammadi–Wortman).
- **Subgroups of `F` or of PL_+(I).** Such an answer would refute the Brin–Sapir
  conjecture (Problem 2.3). Not pursued here; peer lane z2-03-brin-sapir.
- **Residual finiteness (reduction landed).**
  `tf-finf-infinite-cd-omits-f-via-residual-finiteness` derives this claim from
  `some-rf-torsion-free-f-infinity-group-has-infinite-cd`, using the proved
  `thompson-f-is-not-residually-finite`.
- **Guba–Sapir diagram groups** over finite complete presentations. They are
  torsion-free, F_∞ in Farley's setting (not re-read), and often of infinite cd.
  - The artifact computes `D(⟨x,a,b,c | x = xa, a = b, b = c, c = a⟩, x) ≅ ⊕_N Z`.
    That group has infinite cd but is infinitely generated, because nothing shifts
    the spherical pieces back.
  - The open crux: does every finite complete presentation whose diagram group is
    finitely generated and infinite-dimensional contain the binary splitting of
    `x = x²` that produces `F`?
