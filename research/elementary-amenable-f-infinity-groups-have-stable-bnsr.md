---
rg: 2
id: elementary-amenable-f-infinity-groups-have-stable-bnsr
kind: claim
title: "Every elementary amenable group G of type F_infinity has some n with Sigma^m(G) = Sigma^n(G) for all m >= n"
distinct_from:
  virtually-finite-cd-f-infinity-groups-have-stable-bnsr: that claim assumes a finite-index subgroup of finite cohomological dimension; this one assumes only elementary amenability, and the finite-cd subgroup is supplied by the Kropholler–Martínez-Pérez–Nucinkis theorem
  every-f-infinity-amenable-group-is-elementary-amenable: that claim is the open question whether amenable F_infinity groups are elementary amenable; this one is a statement about BNSR invariants of the elementary amenable ones
---

Let `G` be an elementary amenable group of type `F_∞`. Then there is `n ≥ 1`
with `Σ^m(G) = Σ^n(G)` for all `m ≥ n`.

- **Soluble groups.** All soluble groups of type `F_∞` are included.
- **Zaremsky Problem 1.18.** No elementary amenable group answers it
  affirmatively. A properly nested chain needs a group outside the elementary
  amenable class.
- **Zaremsky Problem 1.12.** An amenable affirmative answer to 1.18 would
  also be an amenable, non-elementary amenable group of type `F_∞`, the
  existence answer to 1.12.

Proof: `elementary-amenable-stable-bnsr-via-type-vf`.
