---
rg: 2
id: permuted-free-product-linton-radical-gives-sofic-shell
kind: claim
title: A Linton radical split as a free product permuted by the free shell with cyclic stabilizers gives a sofic shell, and a halo when the permutation is free
distinct_from:
  linton-radical-has-equivariant-sofic-halo: that asks for a sofic set halo for every one-relator group and stays open; this produces one only when the radical already splits as a free product of freely permuted isomorphic factors.
  linton-radical-sofic: that asks whether every Linton radical is sofic; this assumes the factors of a given free splitting are sofic and concludes soficity of the whole shell.
  berlai-perfect-linton-radicals-are-sofic: that closes one explicit family, whose shell is cyclic and whose radical is a finite free product of residue-class chains; this is a permanence theorem for any free splitting permuted by a free shell with cyclic point stabilizers.
  one-relator-soficity-localizes-at-rational-derived-stage: that produces the shell and proves G sofic iff E sofic; this decides E in the split case.
artifacts:
  - research/artifacts/or-linton-halo-2026-09-12.md
---

Let `G = F/<<w>>` be a one-relator group with Linton radical `R`, and let

    E = G_Q^(n) = R semidirect_alpha F0 ,   F0 <= E free,
    alpha(f)(rho) = f rho f^-1 ,

be the finite rational-derived shell of
[[one-relator-soficity-localizes-at-rational-derived-stage]].  Suppose that `R`
is an internal free product

    R = *_{x in X} R_x

indexed by an `F0`-set `X` with `f R_x f^-1 = R_{f.x}` for all `f` in `F0` and
`x` in `X`.  Suppose also that every point stabilizer `S_x <= F0` is cyclic
(possibly trivial).

1. **Star decomposition.**  Choose orbit representatives `x_i (i in I)`, and
   put `S_i = S_{x_i}` and `P_i = R_{x_i} S_i <= E`.  Then `E` is isomorphic to
   the fundamental group of the star of groups with centre `F0`, leaves `P_i`
   and edge groups `S_i`.
2. **Soficity.**  If every `R_x` is sofic, then `E` and `G` are sofic.
3. **Halo.**  Suppose every `S_x` is trivial and every `R_x` is isomorphic to
   one sofic group `K`.  Then `Y |-> *_Y K` is a set-theoretic halo of groups
   in the sense of Alekseev--Bradford (arXiv:2601.18742v1, Definition 2.4)
   with sofic finite pieces.  It carries an `F0`-equivariant isomorphism
   `*_X K -> R`.  So the conclusion of
   [[linton-radical-has-equivariant-sofic-halo]] holds for `G`.
4. **Trivial shell.**  If `F0 = 1`, that conclusion for `G` is equivalent to
   `R` being sofic.

Scope.

- Baumslag--Gersten `G(1,2)` satisfies (4) with a sofic radical.
- `G(1,2) * Z` satisfies (3), with `F0 != 1` and all stabilizers trivial.
- Both groups were already known to be sofic.  The theorem does not exhibit a
  new sofic one-relator group.  It isolates the one shape of radical where the
  halo machinery provably runs.
- It gives nothing when `R` meets a Magnus edge group.

A proof is in
`research/artifacts/or-linton-halo-2026-09-12.md`, Section 4.
