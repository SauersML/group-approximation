---
rg: 2
id: kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures
kind: claim
title: A Kazhdan subgroup of nV is finite iff every nonempty closed invariant subset of the Cantor cube carries an invariant probability measure
distinct_from:
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that asks for finiteness of every Kazhdan subgroup of nV outright; this proves finiteness under the extra hypothesis that all closed invariant sets are measured, and shows that hypothesis is necessary, so it reduces that hole to a statement about invariant measures without settling it.
  heisenberg-in-nv-forces-drift-free-central-element: that uses invariant measures of the same slope (offset) cocycle to find drift-free elements of Heisenberg and BS(1,k) subgroups; this applies property (T) to the slope cocycle in the Koopman representation of an invariant measure and transports deep bricks along the resulting integer potential.
  fw-subgroups-of-eventually-similar-groups-virtually-embed: that proves finiteness of FW subgroups for canonical similarities of one shift through a commensurated set of cones; this works in the product cube of nV, where no commensurated set is known, through almost invariant l2 vectors on marked clopen pieces built from an invariant measure.
artifacts:
  - research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md
---

**ESTABLISHED** by `kazhdan-nv-measure-criterion-proof` (unreviewed by a verifier
lane as of 2026-09-17).

## Setting

- `C = {0,1}^ω`, `n >= 1`, and `nV` acts on `C^n` by homeomorphisms that are
  piecewise canonical on finite brick partitions.
- For `K <= nV`, let `U_K` be the set of points of `C^n` having a clopen
  neighbourhood fixed pointwise by some finite-index subgroup of `K`. It is open and
  `K`-invariant.

## Statement

Let `K <= nV` have property (T).

1. **Invariant measures live on the locally virtually trivial part.** Every
   `K`-invariant Borel probability measure `ν` on `C^n` satisfies `ν(U_K) = 1`.
2. **Criterion.** The following are equivalent:
   - `K` is finite;
   - `U_K = C^n`;
   - every nonempty closed `K`-invariant subset of `C^n` carries a `K`-invariant
     Borel probability measure;
   - every minimal closed `K`-invariant subset of `C^n` carries one.
3. **Shape of a counterexample.** If `K` is infinite, `Z_K = C^n \ U_K` is a nonempty
   closed invariant set with no `K`-invariant probability measure, and no point of
   `Z_K` has a clopen neighbourhood fixed pointwise by a finite-index subgroup.

## Mechanism

- The slope cocycle `s(g,x) ∈ Z^n` (prefix-length change of `g` at `x`) is a bounded
  1-cocycle in the Koopman representation on `L^2(ν)^n`. By Delorme–Guichardet it is a
  coboundary, and it can be corrected to an integer potential `F`.
- The brick of shape `c·1 + F(x)` containing `x`, with its canonical chart, is carried
  by `g` to the one at `gx` off a set of small measure. Pushing `ν` forward gives
  almost invariant unit vectors in `l^2` of the `K`-set of (clopen set, chart) pairs.
- Property (T) pushes their mass onto finite orbits; a pair with finite orbit has a
  finite-index stabilizer that is the identity on the clopen set.

## Imports

- Delorme–Guichardet, (T) iff (FH) for countable discrete groups (Bekka–de la
  Harpe–Valette, *Kazhdan's Property (T)*, Theorem 2.12.4), and the defining form of
  property (T) with a Kazhdan pair. Standard, not re-read at source.
