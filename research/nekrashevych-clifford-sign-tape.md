---
rg: 2
id: nekrashevych-clifford-sign-tape
kind: claim
title: A Thompson-Nekrashevych frame internalizes the twisted Clifford sign tape
distinct_from:
  self-similar-clifford-quantum-expander-tape: that additionally demands a fixed set of word templates giving a uniform quantum-expander gap; this supplies the tree transport, addressing, cocycle, and relative Clifford cells.
  leavitt-cylinder-swaps-generate-thompson-in-el: that realizes ordinary Thompson cylinder swaps in the Leavitt elementary group; this adds a nontrivial self-similar Clifford kernel and central extension.
artifacts:
  - research/artifacts/trace-promotion-renormalization-program-2026-08-20.md
---

Using `self-similar-central-sign-cocycle`, construct a finitely presented
Thompson--Nekrashevych frame (a Rover group or an equivalent finitely
presented central-product Thompson extension) with the following verified
interfaces.

1. Operators supported on disjoint binary cylinders commute as consequences
   of the finite presentation.
2. Any two equal-depth cylinders are conjugate by internal tree isometries;
   normalized trace and HS norm of transported carriers are therefore equal.
3. A site at depth `n` and its local Pauli pair are addressed by words of
   length and derivation area polynomial in `n`, hence polylogarithmic in the
   number of level-`n` sites.
4. The cocycle sign, sibling swaps, and transported Pauli pair realize one new
   relative CAR qubit per level without imposing cross-context commutation on
   old and new selector centers.
5. The exact non-CE tracial model extends to the frame and retains a
   nonidentity marked word.

The ordinary Leavitt/Toeplitz atlas is the trivial-kernel control case.  It
supplies the prefix geometry but not clauses 4--5.

## Attempts

- Start from the prefix swaps in
  `leavitt-cylinder-swaps-generate-thompson-in-el` and replace the trivial
  state group by a finite-state Clifford automaton.
- `thompson-v-central-extensions-split` rules out placing the sign in a
  projective double cover of the prefix-mixer subgroup itself.  The finite
  state kernel is essential: the Thompson letters can only permute or
  transport its local Clifford phases.
- Finiteness of the presentation can be checked from contraction/nucleus data
  once an automaton is fixed.  The explicit central-product construction now
  bypasses that search and obtains finite presentation instead from the
  finite-orbit permutational-wreath theorem.
- A plain `J=(J,J)` automorphism is rejected before presentation work; it is
  the exact untwisted sign obstruction, not a near solution.
- The kernel gate is now solved by
  `thompson-clifford-central-product-tape`: two child CAR groups share one
  center by central amalgamation, and Thompson prefix swaps exchange them.
  What remains for this stronger node is coupling that frame to the exact
  non-CE BCS model and proving the relative sibling-factor placement used by
  the matrix soundness ledger.
