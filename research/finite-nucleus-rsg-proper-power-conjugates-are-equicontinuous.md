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
3. **Bi-Lipschitz exponents and weighted similarities** (2026-09-13, lane
   `solve-rsg-equicontinuity`). *Two sub-cases settled; the general case is
   reduced, not proved.*
   - **Input 1, bi-Lipschitz form.**
     - `bilipschitz-proper-power-conjugates-have-zero-periodic-exponents`: for any
       bi-Lipschitz action, a proper-power relation kills the asymptotic
       Lipschitz exponents at every periodic point. The bound needed is
       `C_g`, not a bound on normalized shifts.
     - `bilipschitz-finite-nucleus-rsg-proper-power-germs-are-torsion`: if some
       positive edge weighting makes every nuclear map bi-Lipschitz, the germs
       of `g` at all rational periodic points have finite order, with no
       finite-orbit hypothesis.
     - The involution `q` of the artifact is bi-Lipschitz for `w(0) = 2`,
       `w(1) = 1`.
   - **Input 2, exact similarities.**
     `weighted-similarity-proper-power-conjugates-are-equicontinuous` runs the
     graph pumping proof for positive edge weights, without surjectivity. So the
     target holds when every nuclear map is a `w`-similarity.
   - **Exact gap.**
     - (a) **Pumping for bi-Lipschitz, non-similarity nuclei.** The pumped cone
       is mapped by a composite of `D` nuclear maps along an orbit. Pair-lag
       errors of up to `K` per step add up to `DK`, while the pigeonhole only
       guarantees an increment `Δ ≥ 1`, so the contraction step fails. An exact
       cocycle with uniformly bounded pair error would repair it. That needs a
       potential `P` on `Nuc` and weights `w` with
       `P(strip(pq)) = P(p) + P(q) + w(lcp(pq(C)))` for composable nuclear `p, q`.
       No such `P` is known.
     - (b) **Existence of bi-Lipschitz weights.** For a single nuclear map this
       amounts to zero net weight on the cycles of its transducer. Rates at
       rational fixed points are `1`, because germ groups there are virtually
       cyclic (observation, not landed). Realizing the rate coboundary by edge
       weights, or by block weights as for maps like `01 → 1`, `1 → 01`, is not
       proved.
     - (c) **Irrational periodic points.** Not addressed.
   - **Not done.** The counterexample search on small graphs was not run, and
     the BBMZ TeX was not re-read: the MSI search for it timed out.
