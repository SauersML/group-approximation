---
rg: 2
id: labbe-torus-tiling-algebra-has-scale-one-module
kind: claim
title: Some finite torus carries a nonzero finite-dimensional module of the scale-1 torus tiling algebra of Labbé's Wang shift over F_q
distinct_from:
  labbe-tiles-admit-periodic-quantum-tilings-at-every-scale: that asks for periodic families at every scale over some field; this asks for one torus module at scale 1 over a finite field, which (with the one-scale theorem) gives modules at every scale over F_q
  labbe-torus-tiling-algebra-has-no-scale-one-module: that is the negation
  labbe-wang-shift-crossed-product-is-exactly-matricial: that is the ring question; this is its equivalent scale-1 form via labbe-ring-matricial-iff-scale-one-torus-module
artifacts:
  - research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md
---

**OPEN.** Let `Ω_U` be Labbé's 19-tile Wang shift and `q` a prime power. Is there a finite-index `Λ ≤ Z^2` such that
`𝒯_(1,Λ)(Ω_U, F_q)` has a nonzero finite-dimensional module? The relations are:
- (T1) partition of unity at each site;
- (T2) commutation for site differences in `B_2`;
- (T3) products over `B_1` of `3×3` patterns that are not globally legal vanish.

The answer depends only on the characteristic `p`.

**Payoff.** Yes decides row 7 positively: `LC(Ω_U,F_q) ⋊ Z^2` is exactly matricial
(`labbe-ring-matricial-iff-scale-one-torus-module`). By `matricial-aperiodic-sft-rings-are-not-quantum-rigid` there are
then periodic quantum tilings at every scale, and neither `D([[Ω_U]])` nor the crossed product is finitely presented.

## Attempts

- **Commutative modules: dead.** A commutative module has a joint atom, which is a `Λ`-periodic legal configuration.
  `Ω_U` has none (the classical-families firewall of `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`).
- **Thin tori: dead.** By `thin-cylinder-sft-tiling-families-force-periodic-points` at `D = 1`, a family periodic along
  an axis with period `<= 5` is zero. So both axis periods of `Λ` are `>= 6`.
- **Narrow strips: must be contextual.** By `strip-commutative-tiling-families-force-periodic-points` and
  `aperiodic-sft-torus-modules-are-contextual-in-every-direction`, site idempotents do not all commute inside strips of
  width `3` along the axes, nor along any rational direction.
- **Growth gives nothing at fixed scale.** `sft-tiling-module-dimensions-and-periods-must-diverge` forces divergence
  only along scales `D -> ∞`. At scale `1` it only says that the period torus has sup-diameter `> 2`.
- **Inflation (swarm-labbe-wang-shift-crossed-produ, 2026-09-16, unreviewed).** One module here gives modules at every
  scale over `F_q` (`morphism-towers-double-covariant-tiling-scales` with `ω^2`, then restriction and descent). So
  this claim is equivalent to its every-scale form. Conversely, showing that no torus carries a module at some fixed
  scale `D` refutes it.
- **Searches not run.** A search needs:
  - tori with both periods `>= 6`, i.e. `>= 36` sites with `19` idempotents each;
  - the legal `3×3` language of `Ω_U` (computable from `labbe-ball-legality-is-pairwise-at-radii-two-to-seven`);
  - noncommutative simple factors.

  That is beyond single-threaded budgets without further structure.
