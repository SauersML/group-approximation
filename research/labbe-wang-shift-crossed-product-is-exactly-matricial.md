---
rg: 2
id: labbe-wang-shift-crossed-product-is-exactly-matricial
kind: claim
title: The Labbé Wang shift crossed product LC(Omega_U, F_q) ⋊ Z^2 embeds unitally in an algebraic ultraproduct of matrix algebras over fields
distinct_from:
  labbe-wang-shift-crossed-product-is-not-exactly-matricial: that is the negation, which finite presentation of the crossed product would force
  labbe-tiles-admit-periodic-quantum-tilings-at-every-scale: that asks only for periodic quantum tilings at every scale; this asks for an exact ring embedding, which yields such tilings and more
  free-minimal-subshift-elementary-groups-are-simple-kazhdan: that gives a unital rank-metric model, hence linear soficity; this asks for an exact algebraic model, which would give LEF groups
---

**OPEN.** Let `Ω_U` be Labbé's Wang shift and `R = LC(Ω_U, F_q) ⋊ Z^2`. Does `R` embed as a unital ring in an algebraic
ultraproduct `∏_ω M_(d_k)(F_k)` of matrix algebras over fields?

**Win-win.**
- **If yes.**
  - Periodic quantum tilings exist at every scale (`matricial-aperiodic-sft-rings-are-not-quantum-rigid`), so neither
    `D([[Ω_U]])` nor `R` is finitely presented.
  - Every `GL_n(R)` is LEF (`exactly-matricial-rings-have-lef-general-linear-groups`), including the topological full
    group in the units.
- **If no.**
  - `R` is a simple, finitely generated, stably finite ring that is not exactly matricial.
  - Its elementary groups (simple mod centre, Kazhdan, linear sofic) decide between
    `stably-finite-simple-rings-have-mf-elementary-groups` and `stably-mf-elementary-groups-force-matricial-rings`.

## Attempts

- **Permutation models: dead.** A model in which the translations act by permutation matrices on a basis refining the
  tile idempotents is a finite genuine `Z^2`-action with legal local patterns. Theorem A of
  `research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md` then gives a periodic point, which `Ω_U` lacks.
- **Commutative families: dead.** A periodic tiling in which all idempotents commute yields a legal periodic tiling (a
  joint atom), the classical-families firewall of `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`. So every
  exact model is contextual at some large distance, while classical within distance `2D`.
- **Dimension counts: no obstruction.** Integer-valued shift-invariant pattern dimensions `dim V_w` exist, since
  rational invariant measures on bounded patterns do. Counting alone cannot refute an exact model.
- **Through finite presentation: reduces to gate (a).** By `matricial-aperiodic-sft-rings-are-not-quantum-rigid`, a
  positive answer to `labbe-wang-shift-crossed-product-is-finitely-presented` gives a negative answer here.
- **Exact form (un-labbe-ring, unreviewed).** Over `F_q` this claim is equivalent to: for every `D` some finite torus
  `Z^2/Λ` carries a nonzero finite-dimensional module of the translation-free torus tiling algebra
  `𝒯_(D,Λ)(Ω_U, F_q)` (`torus-quantum-tilings-decide-matriciality-of-sft-rings`). Translations are recovered by
  induction.
- **Growth (un-labbe-ring, unreviewed).** Any witnesses need period tori of sup-diameter `> 2D`, and covariant
  dimensions `-> ∞` along the scales (`sft-tiling-module-dimensions-and-periods-must-diverge`). In the limit, ranks
  are forced toward the Haar-coded measure, which is not a contradiction.
- **Soficity certificates give nothing here (un-sofic-not-lef, relayed).** `Z^2` is residually finite. Full-group units
  certify non-LEF only if the derived full group is not LEF, which is the open crux (C2). So the quantum tiling route
  is the only way known to decide this claim.
