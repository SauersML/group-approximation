---
rg: 2
id: linton-halo-conclusion-fails-at-shallow-derived-stages-proof
kind: route
title: A contracting ascending-HNN letter in the shell forbids a halo, and deeper shells permute the free factors freely
target: linton-halo-conclusion-fails-at-shallow-derived-stages
requires: [halo-shell-invariant-conjugations-are-virtually-inner, permuted-free-product-linton-radical-gives-sofic-shell, one-relator-soficity-localizes-at-rational-derived-stage]
artifacts:
  - research/artifacts/linton-halo-contraction-obstruction-2026-09-16.md
---

Full proofs are in Sections 4--6 of the artifact.  The word identities are
checked by
`experiments/linton-halo-contraction-obstruction-2026-09-16/check_words.py`.

*Stage independence of the imported theorem.*  The statement of
[[permuted-free-product-linton-radical-gives-sofic-shell]] is phrased for "the"
shell `E = G_Q^(n) = R semidirect F0` of the localization claim.  Its proof
(Section 4 of `research/artifacts/or-linton-halo-2026-09-12.md`) uses only that
`E` is normal in `G` with `G/E` solvable, that `R` is normal in `E` and that
`F0 <= E` is a free complement.  All of these hold at every valid stage `n`.
So parts 2--4 are applied below at the stage named in each case.

**`G0`.**  Put `a_i = s^i a s^-i`.  The relation reads
`a_(i+1) = [a_i, a_(i-1)]` for all `i`.

- *HNN form.*  Eliminating `y = s x s^-1` from
  `< x, y, s | s x s^-1 = y, s y s^-1 = [y,x] >` gives the presentation of
  `G0`.  So `G0 = B *_phi` with `B = F(x,y)` and `phi(x) = y`,
  `phi(y) = [y,x]`.
- *`phi` is injective.*  `phi(B) = < y, x y x^-1 >`, and this generating set
  is Nielsen reduced.  A surjection `F2 -> F2` is injective (Hopfian).
- *`phi` is not onto.*  `phi(B)` lies in the normal closure of `y`, and `x`
  does not.
- *The radical.*  `R = <<a>> = ker(G0 -> Z)` is the directed union of the
  rank-2 free groups `s^-k B s^k`.  So `R` is nontrivial and locally free.
  Each `a_(i+1)` is a commutator in `R`, so `R` is perfect.
- *Linton radical and stages.*  `G0^ab = Z`, so `G0_Q^(1) = R`, and `R` is
  perfect, so `G0_Q^(n) = R` for all `n >= 1`.  All stages are valid.
- *Stage 0.*  `s B s^-1 = phi(B) < B` with `B` finitely generated in the
  locally free `R`.  Part 4 of
  [[halo-shell-invariant-conjugations-are-virtually-inner]] forbids a halo
  presentation of `G0 = R semidirect <rho s>`, for every `rho` in `R`.
- *Stages `n >= 1`.*  `F0 = 1`.  `R` is locally free, hence sofic.  Part 4 of
  [[permuted-free-product-linton-radical-gives-sofic-shell]] gives the halo
  `Y -> *_Y R`.
- *Soficity.*  Part 2 of that claim with `X` a point and stabilizer `Z` makes
  `G0` sofic.

**`G_u`.**  Let `C = <u>` and `F = F(p,q)`.  Substituting `s = u` into the
relator of `G0` gives the presentation of `G_u` as the amalgam
`G0 *_(s = u) F` over `Z`.

- *Free splitting.*  Let `psi : G_u -> F` be the identity on `F`, kill `R0`
  and send `s` to `u`.  Its kernel `K` is `<<a>>`, since `G_u/<<a>> = F`.  In
  the Bass--Serre tree:
  - `K` meets the edge stabilizers (conjugates of `C`) and the conjugates of
    `F` trivially;
  - `K` meets `g G0 g^-1` in `g R0 g^-1`;
  - since `G_u = K semidirect F`, the quotient `K \ T` is a star with centre
    `F/F` and leaves and edges indexed by `F/C`.

  Trivial edge groups on a tree give `K = *_(gC in F/C) g R0 g^-1`.  Free
  products of perfect groups are perfect.  A finitely generated subgroup of a
  free product of locally free groups is free.  So `K` is perfect and locally
  free.
- *Linton radical and stages.*  `F_Q^(omega) = 1`, so `G_Q^(omega) <= K`.  A
  perfect normal subgroup lies in every `G_Q^(i)`, so `K = R`.  By the lemma
  of [[one-relator-soficity-localizes-at-rational-derived-stage]],
  `G_Q^(n)/R = F^(n)`, which is free.  So every stage is valid, with
  complement `F^(n)`.
- *`n <= d`.*  `u` lies in `F^(d) <= F^(n) <= G_Q^(n)`, and
  `u B u^-1 = phi(B) < B` with `B <= R0 <= R`.  Part 4 of
  [[halo-shell-invariant-conjugations-are-virtually-inner]] forbids a halo
  presentation for any complement.
- *`n >= d+1`.*  `F^(n)` acts on `F/C` with stabilizers
  `g (F^(n) cap C) g^-1`.  If `u^k` lay in `F^(n) <= F^(d+1)` with `k != 0`,
  then `u` would lie in `F^(d+1)`, since `F^(d)/F^(d+1)` is torsion-free.  So
  the stabilizers are trivial.  The factors `g R0 g^-1` are all isomorphic to
  the sofic group `R0`.  Part 3 of
  [[permuted-free-product-linton-radical-gives-sofic-shell]] gives the halo
  `Y -> *_Y R0` with an `F^(n)`-equivariant isomorphism onto `R`.
- *Soficity.*  The `F`-stabilizers `g C g^-1` are cyclic, so part 2 of the same
  claim makes `G_u` sofic.

**Consequences.**

- The least valid stage of `G0` is `0`, where the conclusion fails.
- For `G_u` the conclusion fails at all `n <= d`.  Since `d` is arbitrary, the
  least stage with a halo presentation is unbounded.
- Every example satisfies the conclusion at all stages `n >= d+1`.
- At every stage `n`, `G` is sofic iff `G_Q^(n)` is sofic.  The argument of
  part 3 of the localization claim uses only that `G/G_Q^(n)` is solvable, so
  it applies at every `n`.
