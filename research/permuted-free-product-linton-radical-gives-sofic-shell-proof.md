---
rg: 2
id: permuted-free-product-linton-radical-gives-sofic-shell-proof
kind: route
title: Read the split shell off the Bass--Serre tree of a star of groups
target: permuted-free-product-linton-radical-gives-sofic-shell
requires: [one-relator-soficity-localizes-at-rational-derived-stage]
artifacts:
  - research/artifacts/or-linton-halo-2026-09-12.md
---

**(1)**  Let `pi_1(P)` be the star of groups with centre `F0`, leaves
`P_i = R_{x_i} S_i` and edges `S_i`.  Here `R_{x_i} cap S_i <= R cap F0 = 1`,
so `P_i = R_{x_i} semidirect S_i`.

- Let `Phi: pi_1(P) -> E` be the identity on `F0` and on each `P_i`.
- Let `psi: pi_1(P) -> F0` be the identity on `F0` and the projection
  `P_i -> S_i`.
- With `p: E -> F0` the quotient by `R`, `p Phi = psi` on generators.

`ker(psi)` acts on the Bass--Serre tree `T`.

- An edge stabilizer is conjugate to some `S_i`, on which `psi` is injective,
  so the kernel meets it trivially.
- The kernel meets conjugates of `F0` trivially, and meets `g P_i g^-1` in
  `g R_{x_i} g^-1`.

Since `pi_1(P) = ker(psi) semidirect F0`, the kernel has one orbit of central
vertices.  Leaf vertices and edges of type `i` are both indexed by `F0/S_i`,
and the edge `f S_i` joins the centre to the leaf `f S_i`.  The quotient graph
is a star, which lifts to the subtree of `T` spanned by the vertex `F0`, the
vertices `f P_i` and the edges `f S_i` with `f in F0`.  So

    ker(psi) = *_{i} *_{f S_i in F0/S_i} f R_{x_i} f^-1 .

`Phi` maps `f R_{x_i} f^-1` onto `R_{f.x_i}`, and `f S_i |-> f.x_i` is a
bijection from the disjoint union of the `F0/S_i` onto `X`.  Because `R` is the
free product of the `R_x`, `Phi` restricts to an isomorphism
`ker(psi) -> ker(p) = R`.  It is the identity on the complement `F0`, so `Phi`
is an isomorphism.

**(2)**  Each `P_i` is sofic-by-cyclic, hence sofic.  A finite sub-star is an
iterated amalgam of sofic groups over amenable subgroups, hence sofic
(Elek--Szabo, *Sofic representations of amenable groups*, arXiv:1010.3424,
Theorem 1).  The fundamental group of the star is the directed union of its
finite sub-stars, which embed by normal forms, so `E` is sofic.  `G/E` is
solvable, so `G` is sofic by part 3 of
[[one-relator-soficity-localizes-at-rational-derived-stage]].

**(3)**  An injection `j: Y -> Y'` maps the factor `K_y` identically onto
`K_{j(y)}`.  This defines a functor from sets with injections to groups with
monomorphisms.

- Monotonicity and generation by finite pieces are clear.
- `*_Y K cap *_Z K = *_{Y cap Z} K` by uniqueness of reduced forms.
- Trivial factors form whole orbits and can be discarded.  Then `X` is
  countable, because a nontrivial element lies in at most one factor.

Fix isomorphisms `iota_i: K -> R_{x_i}`.  Each `x` equals `f.x_i` for a unique
`i` and a unique `f`, because stabilizers are trivial.  Let `theta` be
`alpha(f) iota_i` on `K_x`.

- `theta` maps `K_x` onto `R_x`, so it is an isomorphism.
- For `g` in `F0`, the functorial automorphism maps `K_x` identically onto
  `K_{g.x}`, and `g.x = (gf).x_i`.  So `theta` after it equals
  `alpha(gf) iota_i = alpha(g) theta` on `K_x`.

Finite free products of sofic groups are sofic (the amalgam theorem over the
trivial group).

**(4)**  Take `X` a point, `L(Y) = *_Y R` and `theta` the identity.  All finite
pieces are sofic iff `R` is.  Conversely, a halo with sofic finite pieces makes
`R` sofic by [[linton-halo-gives-radical-sofic]].
