---
rg: 2
id: finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous
kind: claim
title: In a rational similarity group with finite nucleus, every element conjugate to a proper power generates an equicontinuous cyclic group
distinct_from:
  graph-path-almost-automorphism-proper-power-is-equicontinuous: that is the established statement for almost-automorphism groups of graph path spaces, whose local actions are isometries; this asks the same for RSGs with finite nucleus, whose local actions can change lengths and need not be surjective.
  rsg-proper-power-conjugate-germs-torsion-at-finite-orbits: that is the established pointwise germ statement at rational periodic points with finite orbit under the conjugator; this is the global equicontinuity statement.
artifacts:
  - research/artifacts/bh-bg-rsg-nonisometric-hosts-2026-09-13.md
---

**OPEN.** Let `G ≤ R_{Γ,E}` be a rational similarity group with finite nucleus, in
the sense of Belk--Bleak--Matucci--Zaremsky, arXiv:2309.06224v3. Let `f, g ∈ G`
and nonzero integers `k, l` with `|k| ≠ |l|` satisfy `f g^k f^-1 = g^l`. Is the
family `{g^m : m ∈ Z}` equicontinuous on `E`?

**If true.** `E` is compact, zero-dimensional and metrizable.
- **`BG`.** Every homomorphism from the Baumslag--Gersten group into such a `G`
  kills `a`, by `baumslag-gersten-equicontinuous-generator-acts-trivially`. So no
  finite-nucleus RSG, and no finitely presented simple group inside one, contains
  `BG`.
- **`H4`.** Every homomorphism from Higman's group `H4` into such a `G` is
  trivial. This uses the triviality step of
  `higman-group-graph-host-obstruction-proof`, which needs only equicontinuous
  generators on a compact zero-dimensional space.
- **Reach.** Both exclusions would cover the full, contracting RSGs of BBMZ.
  These contain every hyperbolic group and every contracting Röver--Nekrashevych
  group.

**Known cases.**
- **Isometric local actions.** Almost-automorphism groups of graph path spaces:
  `graph-path-almost-automorphism-proper-power-is-equicontinuous`.
- **Pointwise, finite orbits.** At rational periodic points with finite orbit
  under `f`, the germs of powers of `g` have finite order:
  `rsg-proper-power-conjugate-germs-torsion-at-finite-orbits`.
- **One explicit model.** The dyadic affine model of `BS(1,2)` has a
  non-equicontinuous `a` and no finite-nucleus host:
  `dyadic-affine-bs12-model-lies-in-no-finite-nucleus-rsg`.

**Consistency check.** Hyperbolic groups contain no `BS(k,l)` with `|k| ≠ |l|`. So
the BBMZ embedding of hyperbolic groups gives no counterexample. The Gromov barrier
of `rsg-kazhdan-rf-obstruction-implies-hyperbolic-rf` is about residual finiteness
of Kazhdan subgroups, so it does not apply either.

## Attempts

1. **Transfer the pumping proof** (2026-09-13, lane `solve-bh-rational-similarity`).
   *Fails as it stands.*
   - Items 0, 1, 2(i) and 4 of `graph-almost-automorphism-exponent-pumping-proof`
     each use isometric local actions (§1 of the artifact).
   - The rescaling involution `q` of §1 conjugates an element of `F` with
     canonical-shift exponent `1` to one with exponent `1/2`.
2. **Normalized germ exponents** (same lane). *Reduced, not proved.*
   - Stabilizer rates at rational fixed points are trivial, because germ groups
     are virtually infinite cyclic. So rates form a coboundary on orbits of
     rational points, and exponents normalized by its potential are conjugation
     invariant.
   - Two inputs are missing:
     - a bound on normalized exponents over the periodic points of a fixed
       element;
     - a pumping lemma producing a rational periodic point with infinite-order
       germ from non-equicontinuity.
   - See §3 of the artifact.
