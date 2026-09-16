---
rg: 2
id: halo-shell-invariant-conjugations-are-virtually-inner
kind: claim
title: In a set-halo semidirect product, a conjugation preserving a finitely generated subgroup of the halo is virtually inner there
distinct_from:
  linton-radical-has-equivariant-sofic-halo: that asks for a sofic set-halo presentation of the Linton shell of every one-relator group; this is a necessary condition that every set-halo presentation of every semidirect product obeys, with no soficity and no one-relator hypothesis.
  permuted-free-product-linton-radical-gives-sofic-shell: that constructs halo presentations when the radical is a freely permuted free product; this restricts which shells can have a halo presentation at all.
  site-pullbacks-strict-iff-stabilizer-self-compressed: that classifies one-site equivariant self-maps of coset shifts, which are strict exactly when a stabilizer is properly conjugated into itself; this is about groups rather than shifts, and forbids proper self-conjugation of a finitely generated subgroup of a locally free halo group.
  sofic-halo-products-preserve-hyperlinearity: that is a permanence theorem for halo products with sofic site actions; this is a structural restriction on which semidirect products are halo products.
artifacts:
  - research/artifacts/linton-halo-contraction-obstruction-2026-09-16.md
---

ESTABLISHED.  Let `E = R semidirect F0` with `F0` acting by conjugation, and
suppose `(E, R, F0)` has a *halo presentation*:

- an `F0`-set `X`, via `pi : F0 -> Sym(X)`;
- a set-theoretic halo `L` in the sense of Alekseev--Bradford
  (arXiv:2601.18742v1, Definition 2.4);
- an isomorphism `theta : L(X) -> R` with
  `theta o L(pi(f)) = c_f o theta` for all `f` in `F0`.

1. **Virtually inner.**  Let `e` be in `E` and let `H <= R` be finitely
   generated with `e H e^-1 <= H`.  Then there are `N >= 1` and `rho'` in `R`
   with `e^N h e^-N = rho' h rho'^-1` for all `h` in `H`.
2. **Torsion quotient.**  For every finitely generated `H <= R`, the group
   `N_E(H) / (N_R(H) C_E(H))` is torsion.
3. **No proper self-conjugation in locally free groups.**  If `R` is locally
   free, `H <= R` is finitely generated and `rho` in `R` has
   `rho H rho^-1 <= H`, then `rho H rho^-1 = H`.  This part needs no halo.
4. **No contraction.**  If `R` is locally free and has a halo presentation,
   then no `e` in `E` conjugates a finitely generated `H <= R` properly into
   itself.

Part 1 uses only functoriality on injections, monotonicity and generation by
finite pieces.  It uses neither the intersection axiom nor soficity of the
pieces, and it does not depend on the choice of complement `F0`.  It needs
finitary permutations in the domain of `L`, so it says nothing about graph
halos.

Use.  Part 4 shows that the Linton shell `G_Q^(n)` of a one-relator group with
locally free radical has no halo presentation whenever some element of
`G_Q^(n)` contracts a finitely generated subgroup of `R`.  Explicit instances
are in [[linton-halo-conclusion-fails-at-shallow-derived-stages]].
