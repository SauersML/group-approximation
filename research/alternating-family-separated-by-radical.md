---
rg: 2
id: alternating-family-separated-by-radical
kind: route
title: Recover the simple type from the finite-index-invariant radical
target: alternating-lamp-noncommensurable-family
requires: [compression-wreath-five-radicals-coincide, corona-finite-index-radical-heredity]
artifacts:
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - GroupApproximation/Algebra/PermutationalWreathSimple.lean
---

## Why sufficient

Each `A_n`, `n >= 5`, is finite, nontrivial, and perfect, so the first
prerequisite gives `Rad_MF(W_n) = Res_fin(W_n) = A_n^(G*/Gamma*)` with visible
quotient `G*`, together with all the shared-target clauses.  Soficity is the
finite-index telescope action plus the generalized wreath theorem;
hyperlinearity follows from soficity, since permutation matrices satisfy
`||P_sigma - P_tau||_{2,d}^2 = 2 d_Ham(sigma, tau)`, so a Hamming model is a
Hilbert--Schmidt model.

**Noncommensurability.**  Suppose `f : H_m -> H_n` is an isomorphism between
finite-index subgroups.  By the second prerequisite (applied through the
finite residual, which obeys the same finite-index formula) and by
`R <= every finite-index subgroup`, both radicals are unchanged:

    Res_fin(H_m) = A_m^(G*/Gamma*),   Res_fin(H_n) = A_n^(G*/Gamma*).

The finite residual is an isomorphism invariant, so `f` carries one onto the
other and

    A_m^(G*/Gamma*)  =~  A_n^(G*/Gamma*).

Now read off the simple type.  In a nonzero restricted direct sum of copies of
a nonabelian simple `S`, every nonabelian simple quotient is isomorphic to
`S`: each coordinate subgroup is normal, so its image is trivial or the whole
target; some coordinate must surject, and a surjection from a simple group
with nontrivial image is injective.  Conversely each coordinate projection
realizes `S`.  Hence `A_m =~ A_n`, and `|A_n| = n!/2` is strictly increasing,
so `m = n`.

**Simplicity input.**  `A_n` simple for every `n >= 5` is proved from scratch
in section 52.1 of the dossier rather than cited.

## Priority

This package — an infinite pairwise noncommensurable family with a fixed
visible approximation theory and the distinguishing invariant confined to the
invisible radical — is the strongest novelty candidate in the dossier.  It is
recorded here as proved; a systematic literature review is still owed before
any "first known examples" wording is used outside the graph.
