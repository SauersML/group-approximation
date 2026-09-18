---
rg: 2
id: hyperbolic-f3-by-z-with-genus-two-surface-certificates
kind: claim
title: The hyperbolic free-by-cyclic groups of a -> abb, b -> ca, c -> babb and a -> abb, b -> caba, c -> babb contain genus-two surface subgroups, certified by legal f-folded fatgraphs
distinct_from:
  legal-f-folded-fatgraphs-give-surface-subgroups: that is the criterion (a legal f-folded fatgraph with chi < 0 gives a surface subgroup); this exhibits verified certificates for explicit hyperbolic mapping tori, so the criterion is not vacuous.
  positive-f-folded-fatgraphs-have-only-even-valence: that bounds certificates (sign parity, gate bound, per-word LP) and certifies that phi_4 and phi_P have no single-word certificates in a range; the automorphisms here pass the gate bound, and their certificates use the two words w and w^-1, which that LP does not cover.
  random-ascending-hnn-of-free-groups-contain-surface-subgroups: that uses immersion endomorphisms, whose mapping tori are never hyperbolic free-by-cyclic groups; these are automorphisms with non-immersion train-track representatives.
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for every one-ended hyperbolic group; this covers 24 explicit hyperbolic F_3 x| Z (two up to relabelling and word reversal).
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_phi1028.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_phi192.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surfaces_m1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_batch.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/find_surface.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/unroll_phi1028_n5.log
---

**ESTABLISHED (computer-certified).** Let `F = F(a, b, c)` and

```text
phi_1 : a -> abb,  b -> ca,    c -> babb      (chi_M = t^3 - t^2 - 5t + 1)
phi_2 : a -> abb,  b -> caba,  c -> babb      (chi_M = t^3 - 2t^2 - 6t + 1)
```

Both are automorphisms of `F`. Both mapping tori `F x|_phi Z` are one-ended hyperbolic groups, and
each contains the fundamental group of the closed orientable surface of genus 2.

The same holds for the 22 further positive automorphisms listed in `surfaces_m1.log`. Each is
`phi_1` or `phi_2` after permuting the letters and/or reversing every image word (conjugating by
`x -> x^-1`), so their mapping tori are isomorphic to those of `phi_1` and `phi_2`. The two
characteristic polynomials and their reciprocals are pairwise distinct, so `phi_1` and `phi_2`
are not conjugate in `Out(F_3)`, not even up to inversion.

Proof: `hyperbolic-f3-by-z-with-genus-two-surface-certificates-proof`.

## The certificate for phi_1

- The boundary `partial^-` is the two circles `bc` and `CB`, so `partial^+` is `f(bc)^-1 = BBABAC`
  and `f(CB)^-1 = cababb`.
- Gluing these 16 boundary letters in pairs gives a fatgraph `X` with 6 vertices of valences
  `2, 2, 2, 2, 4, 4`, 8 edges, `chi(X) = -2`, and one component. The pairing is in
  `surface_phi1028.json`.
- The gates of `f` are `{a}, {b}, {c}, {A, C}, {B}`.
- The two 4-valent vertices have directions `b, B, a, C` and `B, b, C, a`, all in distinct gates.
- Glue `partial^-` to `partial^+` by `f`. The result `S*_f(X)` is a closed orientable surface with
  `chi = -2`, and the criterion `legal-f-folded-fatgraphs-give-surface-subgroups` makes it
  `pi_1`-injective.

## Why it matters

- **First certificates for automorphisms.** Calegari--Walker's immersion criterion never applies
  to a hyperbolic free-by-cyclic group (`automorphism-immersion-representatives-have-finite-order`).
  These are the first finite f-folded certificates on main for the class "hyperbolic free-by-cyclic
  groups". That class is listed as uncovered in `one-ended-hyperbolic-groups-contain-surface-subgroups`.
- **What is known already.** Second-hand only, not read at source: N. Brady and coauthors
  ("Distortion of surface groups in CAT(0) free-by-cyclic groups", Geom. Dedicata 2006) report
  hyperbolic free-by-cyclic groups containing closed surface subgroups. So the existence of *some*
  such group is not new. What is new here:
  - the certificate route through train-track legality;
  - its verification by a short independent checker;
  - the positive answer for these specific atoroidal automorphisms.
- **The certificates are small.** Two 2-letter boundary words and 16 or 20 boundary letters.
  Every hypothesis of the criterion is a local check on a finite pairing, so a search over
  positive automorphisms can hunt for more.
