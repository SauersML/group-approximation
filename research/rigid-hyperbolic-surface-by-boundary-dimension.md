---
rg: 2
id: rigid-hyperbolic-surface-by-boundary-dimension
kind: route
title: Split rigid hyperbolic groups by boundary dimension; Kapovich--Kleiner settles the carpet and circle cases
target: rigid-hyperbolic-groups-contain-surface-subgroups
requires:
  - kapovich-kleiner-one-dimensional-boundary-classification
  - carpet-boundary-hyperbolic-groups-have-surface-subgroups
  - finite-by-cocompact-fuchsian-groups-are-virtually-surface
  - menger-boundary-rigid-hyperbolic-surface-subgroups
  - high-dim-boundary-rigid-hyperbolic-surface-subgroups
---

Let `R` be an infinite hyperbolic group with no nontrivial splitting over a finite or virtually
cyclic subgroup.

## Step 1: `dim ∂R >= 1`

- `R` does not split over a finite subgroup. By Stallings' theorem a finitely generated group with
  more than one end splits over a finite subgroup. `R` is infinite, so it has at least one end,
  and hence exactly one. This is also how Kapovich--Kleiner open their proof of Theorem 4, quoted
  in the import.
- So `∂R` is connected, as in the same quote.
- If `∂R` were finite, `R` would be elementary, that is, finite or virtually `Z`. A virtually `Z`
  group is two-ended. So `∂R` is infinite.
- A compact metrizable space of covering dimension `0` is totally disconnected. `∂R` is compact,
  metrizable, connected and has more than one point, so `dim ∂R >= 1`.

## Step 2: case split

**Case `dim ∂R >= 2`.** This is `high-dim-boundary-rigid-hyperbolic-surface-subgroups`.

**Case `dim ∂R = 1`.** Kapovich--Kleiner Theorem 4 applies verbatim to `R`, giving three
alternatives.

1. **`∂R` is the Menger curve.** This is `menger-boundary-rigid-hyperbolic-surface-subgroups`.
2. **`∂R` is the Sierpinski carpet.** This is
   `carpet-boundary-hyperbolic-groups-have-surface-subgroups`.
3. **`∂R ≅ S^1`, and `R` maps onto a Schwarz triangle group `T` with finite kernel `F`.** We use
   only that `T` is a finitely generated discrete group of isometries of `X`, where `X` is one of
   `S^2`, `E^2`, `H^2`. This holds for a triangle reflection group and for its orientation-
   preserving subgroup, whatever the angles and whether or not vertices are ideal.
   - A surjection of finitely generated groups with finite kernel is a quasi-isometry. So `T` is
     infinite, one-ended and hyperbolic, like `R`.
   - **`X = S^2`.** Discrete subgroups of the compact group `O(3)` are finite. Contradiction.
   - **`X = E^2`.** Discrete groups of isometries of the Euclidean plane are virtually abelian. A
     one-ended finitely generated virtually abelian group contains `Z^2`, so it is not hyperbolic.
     Contradiction.
   - **`X = H^2` and `T` not cocompact.**
     - By Selberg's lemma, `T` has a torsion-free finite-index subgroup `T_0` of orientation-
       preserving isometries acting freely.
     - `H^2/T_0` is a noncompact surface, so `T_0` is free, since noncompact surfaces deformation
       retract onto graphs.
     - An infinite virtually free group has two or infinitely many ends. Contradiction.
   - **Remaining case.** `T` is a cocompact discrete subgroup of `Isom(H^2)`, and
     `1 -> F -> R -> T -> 1` with `F` finite.
     `finite-by-cocompact-fuchsian-groups-are-virtually-surface` gives a finite-index subgroup of
     `R` isomorphic to a closed orientable surface group of genus at least `2`.

In every case `R` contains the fundamental group of a closed surface with `chi < 0`.

Kapovich--Kleiner do not define "Schwartz triangle group" in the extracted text. The phrase
occurs only in Theorem 4 and, spelled "Schwarz", in the proof of Theorem 4. Step 2(3) is written
to work under every reading listed above.
