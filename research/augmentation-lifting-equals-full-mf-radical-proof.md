---
rg: 2
id: augmentation-lifting-equals-full-mf-radical-proof
kind: route
title: A lift is a family of finite-dimensional representations, and the zero map lifts
target: augmentation-lifting-equals-full-mf-radical
requires: []
---

Throughout, `G` has no nontrivial finite-dimensional unitary representation.
Equivalently `I_G` has no nonzero finite-dimensional representation: a
nonzero `*`-homomorphism `I_G -> M_d` extends to `A = C*_max(G)` (an ideal in
a C*-algebra has this extension property for finite-dimensional, hence
nondegenerate-on-a-summand, representations), and a representation of `A` not
killing `I_G` is a representation of `G` that is not a multiple of the
augmentation, i.e. a nontrivial finite-dimensional unitary representation.

**(1) implies (2).**  Let `phi : I_G -> Q` be a `*`-homomorphism and let
`Phi : I_G -> prod_n M_(d_n)` be a lift. Composing with the `n`-th coordinate
projection gives a `*`-homomorphism `I_G -> M_(d_n)`, which is zero by
hypothesis. This holds for every `n`, so `Phi = 0`, and therefore
`phi = pi o Phi = 0`, where `pi` is the quotient map.

**(2) implies (1).**  The zero map is a `*`-homomorphism
`I_G -> prod_n M_(d_n)` lifting the zero map, so every `phi` -- all of which
are zero by (2) -- lifts. The implication is trivial, which is exactly why
(1) carries no information here.

**(2) implies (3).**  Let `rho : G -> U(Q)` be a homomorphism into the
unitary group of a norm matrix corona, and let `pi_rho : A -> Q` be the
induced unital `*`-homomorphism. Its restriction to `I_G` is zero by (2), so
`pi_rho` factors through `A / I_G = C`, i.e. `pi_rho = eps` composed with the
unital inclusion `C -> Q`. Hence `rho(g) = 1` for every `g`, so `ker rho = G`.
Intersecting over all `Q` and all `rho` gives `Rad_MF(G) = G`.

**(3) implies (2).**  Let `phi : I_G -> Q`. Extend it to a `*`-homomorphism
`A -> Q` -- `I_G` has codimension one in `A`, and `A = I_G + C 1`, so
`psi(a) = phi(a - eps(a)1) + eps(a) 1` is the unique unital extension, and it
is multiplicative because `eps` is a character with kernel `I_G`. Then
`g |-> psi(g)` is a homomorphism `G -> U(Q)`, trivial by (3), so `psi = eps`
and `phi = psi|_(I_G) = 0`.

The cycle (1) => (2) => (3) => (2) => (1) closes the equivalence. Every step
is a page of bookkeeping; that is the finding.
