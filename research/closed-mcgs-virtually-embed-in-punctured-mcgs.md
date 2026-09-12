---
rg: 2
id: closed-mcgs-virtually-embed-in-punctured-mcgs
kind: claim
title: For every genus at least three some finite-index subgroup of the closed-surface mapping class group embeds in a punctured-surface mapping class group
distinct_from:
  closed-surface-mapping-class-groups-satisfy-boone-higman: that is the Boone--Higman statement for these groups; this is one sufficient embedding premise for it, into hosts that BFFHZ already handle.
  closed-mcgs-have-no-covering-lift-to-marked-covers: that excludes the covering-lift form of such an embedding in genus at least four; this asks for any injective homomorphism at all.
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

**OPEN.** Let `Σ` be a closed orientable surface of genus `g ≥ 3`. Then there
exist:
- a finite-index subgroup `L ≤ Mod(Σ)`;
- an orientable finite-type surface `Σ′` with at least one puncture or boundary
  component;
- an injective homomorphism from `L` to the extended mapping class group of
  `Σ′`.

This premise feeds `closed-mcg-bh-via-punctured-mcg-host`.

## Attempts

1. **Covering lifts with marked points, the BFFHZ one-puncture template.**
   - *Dies* for `g ≥ 4`, by `closed-mcgs-have-no-covering-lift-to-marked-covers`.
   - In genus 3 it is equivalent to a virtual section of the genus-3 Birman
     sequence (`outer-covering-lifts-are-virtual-sections`). Chen--Salter's
     Theorem A does not decide that case.
2. **Targets of small genus.** *Dies* for the full group when `g ≥ 6`.
   - **Source.** Aramayona--Souto, arXiv:1011.1855v1, abstract, read from the
     PDF on MSI. For `X` of genus `g ≥ 6` and `Y` of genus at most `2g − 1`
     (not closed if its genus is `2g − 1`), "every non-trivial homomorphism
     Map(X) → Map(Y) is induced by an embedding, i.e. a combination of
     forgetting punctures, deleting boundary components and subsurface
     embeddings".
   - **Conventions.** Their `Map` is orientation-preserving and fixes punctures
     and boundary pointwise.
   - **Consequence.** A closed `X` has nothing to forget or delete, and is a
     subsurface only of a closed surface. So `Map(X)` has no nontrivial
     homomorphism to `Map(Y)` for punctured or bordered `Y` of genus
     `≤ 2g − 1`.
   - **Still open.** Finite-index subgroups, extended targets, and targets of
     genus `≥ 2g`.
3. **Covers of closed surfaces without marked points.** Aramayona--Leininger--Souto,
   arXiv:0811.0841v1, abstract: "The first family of examples injects the
   mapping class group of a closed surface into that of a different closed
   surface." Those targets are closed again, so they reduce the problem to
   itself.
