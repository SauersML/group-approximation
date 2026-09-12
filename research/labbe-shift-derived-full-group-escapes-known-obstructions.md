---
rg: 2
id: labbe-shift-derived-full-group-escapes-known-obstructions
kind: claim
title: The derived full group of Labbé's minimal aperiodic Wang shift is f.g. infinite simple and escapes every recorded obstruction
distinct_from:
  elek-monod-near-hit-has-torsion-no-kazhdan-subgroup: That concerns the Elek--Monod edge-colouring system, whose alternating group is non-amenable; this concerns Labbé's minimal aperiodic Wang shift, where amenability is open and every recorded obstruction to a finitely presented simple amenable subgroup fails.
  amenable-full-group-forces-invariant-measure: That kills compressible hosts; this shows the Labbé shift is not compressible, and also escapes the periodic-approximation and residual-finiteness obstructions.
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
---

**ESTABLISHED.** Let `X = Omega_U` be Labbé's 19-tile Wang shift and `Gamma = D([[Z^2 ~ X]])`.

1. `Gamma` is finitely generated, infinite and simple.
2. `X` has an invariant probability measure of full support. So no nonempty clopen set holds two disjoint clopen copies of itself through compact open bisections, and the compressibility obstruction of `amenable-full-group-forces-invariant-measure` does not apply.
3. In `fp-subshift-full-group-subgroups-extend-to-sft` one may take `Y = X`. Its finite-orbit clause is vacuous, because `X` has no finite orbit.
4. `X` has no periodic approximations, and `Z^2 ~ X` is not residually finite. So neither `periodic-approximable-subshifts-host-no-fp-simple-group` nor Xin Ma's Theorem C (arXiv:2209.00580) applies.

Hence `Gamma` is a live candidate for `fp-infinite-simple-amenable-group`. Its amenability (`labbe-shift-derived-full-group-is-amenable`) and finite presentation (`labbe-shift-derived-full-group-is-finitely-presented`) are open.

**Proof sketch.** The full proof is in the artifact, Section 3.
- Item 1 is `minimal-z2-subshift-derived-full-groups-are-fg-simple`, applied through `minimal-aperiodic-wang-shift-exists`.
- Item 2: `Z^2` is amenable, and by minimality the support of an invariant measure is everything.
- Items 3 and 4: `X` is itself an SFT with no finite orbit. Apply `sfts-without-finite-orbits-are-not-residually-finite-actions`.

No novelty is claimed.
