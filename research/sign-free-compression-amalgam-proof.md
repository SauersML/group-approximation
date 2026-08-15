---
rg: 2
id: sign-free-compression-amalgam-proof
kind: route
title: The root coordinate involution is a witness and the vertex group embeds
target: sign-free-compression-amalgam
requires: [compression-torsion-collapse]
artifacts:
  - GroupApproximation/Sofic/InvolutionCollapseEndpoint.lean
---

## Why sufficient

Let `c` be the coordinate involution of `(Z/2)^X` at the root coset
`L_0`.  Inside `G`:

- (W1) `c^2 = 1`.
- (W2) the stabilizer of the root coset in `L` is `L_0 = s L s^{-1}`, so
  `[s L s^{-1}, c] = 1`.
- (W3) the `L`-conjugates of `c` are the coordinate involutions
  `c_{gamma L_0}`, all inside one elementary abelian group, hence pairwise
  commuting.

So `c` is an involutive compression witness for `(L, s)` in `G`, and the
formalized involutive collapse endpoint behind
`compression-torsion-collapse` puts every `[gamma, c]`, `gamma in L`, into
`Rad_MF(G)`.

Choose `gamma in L \ L_0`.  In the vertex group `P`,
`[gamma, c] = c_{gamma L_0} c_{L_0} != 1` because the two coordinates are
distinct.  The normal form for amalgamated free products embeds `P` into
`G`, so the commutator stays nontrivial in `G`.  A nontrivial element of
`Rad_MF(G)` makes every corona representation non-injective.

Finite presentation: `P` is `(Z/2)^m semidirect L` with the finite
permutation action of `L` on `X` presented by finitely many lamp,
commutation, and action relators over a finite presentation of `L`; the
amalgam adds the identification of the two copies of `L`.
