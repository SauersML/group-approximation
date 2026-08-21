---
rg: 2
id: sln-z-flexibly-hs-stable
kind: claim
title: SL_n(Z) for some n at least three is flexibly Hilbert-Schmidt stable
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  sl2-z-inverse-pq-is-hs-stable: that is stability of the three-place S-arithmetic lattice SL_2(Z[1/pq]); this is stability of the plain higher-rank lattice SL_n(Z), a (T) group.
  iwahori-local-global-defect-question: that is (equivalent to) flexible stability of SL_2(Z[1/2]); this is the plain SL_n(Z), covered by neither Dogon nor Dogon-Vigdorovich.
---

Decide whether `SL_n(Z)` (`n >= 3`) is flexibly Hilbert--Schmidt stable
(Dogon--Vigdorovich Def 1.2 / Becker--Lubotzky flexible stability): every
asymptotic unitary representation is, after padding by a vanishing-density
corner, uniformly close to a genuine finite-dimensional representation.

By `sln-z-thin-codense-tau-pair` and
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear`, a positive answer
produces an explicit non-hyperlinear group
`G = <SL_n(Z), t | [t, C] = 1>` (`C` a thin co-dense subgroup).

## Attempts

- **Not ruled out by the (T) obstruction.**  `SL_n(Z)` is an infinite
  hyperlinear Kazhdan group, so it is not STRICT/local HS-stable
  (`infinite-hyperlinear-kazhdan-group-is-not-hs-stable`), but that says
  nothing about FLEXIBLE stability, which is the entire open subject of
  Dogon arXiv:2211.10492.
- **Not ruled out by cohomological obstructions.**  Ioana--Spaas--Wiersma
  (arXiv:2006.01874) LLP/LP obstructions do not reach `SL_n(Z)`; the relevant
  central extensions are finite (`K_2(Z) = Z/2`), and finite extensions of
  hyperlinear groups are hyperlinear, so no ISW-type instability is known.
- **Genuinely open, like every host.**  No infinite (T) group is known to be
  flexibly HS-stable or weakly ucp-stable; this is the shared open core
  (`nonhyperlinear-conditional-routes-landscape`).  The sharpest published
  toolkit toward it is de la Salle arXiv:2204.07084 (finite-group
  exactification with linear dimension-free constants in an arbitrary tracial
  target) plus a length-control estimate for the congruence relator family.
