---
rg: 2
id: compression-defect-finite-dimensional-sterility-proof
kind: route
title: Compressors normalize the commutant, and in finite dimensions injective is surjective
target: compression-defect-dies-in-finite-dimensions
requires: []
artifacts:
  - GroupApproximation/Criterion/CompressionCentralizerDefect.lean
  - research/artifacts/strong-atiyah-audit-2026-08-17.md
---

## Why sufficient

Let `C = { T in End_k(V) : T pi(l) = pi(l) T for all l in L }` be the
commutant of `pi(L)`, a `k`-subspace of `End_k(V)` and finite-dimensional
because `V` is.

For `s in Comp(L)`, `T in C` and `l in L`, using `s l s^{-1} in L`:

    pi(s)^{-1} T pi(s) pi(l) = pi(s)^{-1} T pi(s l s^{-1}) pi(s)
                             = pi(s)^{-1} pi(s l s^{-1}) T pi(s)
                             = pi(l) pi(s)^{-1} T pi(s).

So `Ad(pi(s)^{-1})(C) <= C`.  That map is injective and `C` is
finite-dimensional, hence it is surjective, so `Ad(pi(s))(C) = C`.  Every
element of `G_comp(L)` therefore normalizes `C`.

If `z in C_H(L)` then `pi(z) in C`, so for `g in G_comp(L)` we get
`pi(g z g^{-1}) in C`, which commutes with every `pi(l)`.  Hence each
displayed generator `[g z g^{-1}, l]` maps to `1`.  A kernel is normal, so it
contains the normal closure of the generating set, which is `D(H,L)`.

## Status

Machine-checked, not merely argued: `compressionCentralizerDefect_le_ker`,
with the surjectivity step isolated as
`compressionGroup_le_commutantStabilizer` and the generator computation as
`map_compressionCentralizerDefect_generator_eq_one`.  The Lean definitions are
the ones displayed in the target node.

Note for anyone extending this: the finite-dimensionality hypothesis is spent
only on injective-implies-surjective.  Every extension of this theorem in the
graph is an argument that some other target restores that step, and the
refutation `linnell-skew-field-can-be-centrally-infinite` is an argument that
one cannot.
