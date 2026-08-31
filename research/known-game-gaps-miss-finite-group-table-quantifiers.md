---
rg: 2
id: known-game-gaps-miss-finite-group-table-quantifiers
kind: claim
title: Known nonlocal-game gaps miss the finite group-table quantifiers
distinct_from:
  finite-table-quantum-classical-hamming-gap: that asks for one coherent regular-character multiplication table; this audits the existing exact, gapped, and nonclosed game sources and shows why none currently supplies it.
  exact-finite-dimensional-group-table-classicalizes: that rules out one exact separated unitary table; this combines it with the two other game-value regimes and the explicit permutation model of Slofstra's marked sign.
  perfect-decoding-does-not-imply-quantum-value-gap: that records the existence of a nonclosed LCS game with quantum value one; this checks its natural solution-group table against permutation approximability.
---

**ESTABLISHED SOURCE AUDIT.** None of the finite synchronous/nonlocal-game
sources currently established in Cairn proves
`finite-table-quantum-classical-hamming-gap`. The obstruction is a precise
three-way quantifier mismatch.

1. **Strict finite-dimensional quantum gaps have the wrong first line.** If
   a source model has value `beta` while `omega^q<=beta-gamma`, then no robust
   compiler which turns a unitary table of defect `delta` into a strategy of
   value `beta-O(delta)` can have unitary-table infimum zero. This applies to
   the MIP*/BCS, Manzoor, Lin, and tailored ZPC sources whose soundness
   endpoint is a fixed finite-dimensional quantum gap.

2. **Attained perfect quantum strategies give no group-table gap.** If the
   compiler outputs an exact finite-dimensional separated multiplication
   table, `exact-finite-dimensional-group-table-classicalizes` replaces it by
   an exact finite permutation table. Thus standard perfect-quantum versus
   imperfect-classical games, including finite Pauli/LCS examples, separate
   scalar assignments from operator assignments but not permutation group
   tables from unitary group tables.

3. **The nonclosed LCS regime has the right unitary shape but its natural
   marked table fails.** Slofstra's nonclosed LCS game has

```text
omega^q=1
```

without a perfect finite-dimensional strategy, so it is the only established
game source above that can even support an unbounded-dimensional
defect-to-zero sequence. But for the solution group used in that
construction, `slofstra-involution-not-sofic-radical` gives permutation
ultraproduct models in which the distinguished sign `J` survives. Hence the
natural marked multiplication table cannot have a positive permutation
Hamming floor detected by `J`.

The last statement is deliberately scoped: the permutation-ultraproduct map
need not be faithful on the whole solution group, so it does not refute every
possible larger regular-character table extracted from the nonclosed game.
It proves that the obvious central-sign table and the usual classical game
gap do not suffice. A new candidate would need both:

```text
(GT1) a finite-dimensional, normalized-HS, defect-to-zero table sequence
      with the full regular-character separation profile;
(GT2) a decoder from every low-Hamming permutation table to the forbidden
      classical object, or another direct permutation lower bound.          (KGG1)
```

Existing game-value soundness supplies neither pair simultaneously. In
particular `C_qc\C_qa` correlations fail `(GT1)`, while a classical-value gap
alone is not `(GT2)`: permutation matrices are noncommuting finite-dimensional
operator models, not pointwise deterministic game assignments.

There is nevertheless one precise continuation. For any selected Slofstra
`C_qa` character, mixing it with the trivial character and taking conjugate
tensor powers gives the regular-character models required by `(GT1)` for
`H=S/ker(pi_chi)`. But the natural character obtained from the negative
corner of Slofstra's permutation-valued construction has a **sofic** image by
`slofstra-natural-negative-corner-image-is-sofic`. The only remaining
possibility is an alternative perfect-`C_qa` character satisfying
`slofstra-tracial-image-has-radical-word`. Finding it is exactly the missing
hyperlinear-nonsofic quotient, not a consequence of nonclosure alone.

DERIVATION
known-game-gap-table-audit-proof
