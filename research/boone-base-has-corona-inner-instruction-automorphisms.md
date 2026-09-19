---
rg: 2
id: boone-base-has-corona-inner-instruction-automorphisms
kind: claim
title: The Boone base admits one corona embedding implementing every instruction automorphism
distinct_from:
  benign-witness-finite-quotients-refine-the-fold: that is the profinite hole of the Higman-witness route; this is the corona hole of the Aanderaa-Boone route, about an explicit amalgam of Baumslag-Solitar groups free-multiplied with a free group.
  boone-instruction-twists-extend-to-base-automorphisms: that proves the twists are automorphisms and reduces MF of the Boone group to this statement; this is the statement.
---

Let `B = G_1 * F(Q cup {q})` with `G_1 = *_<x> BS(1,2)_s` (`s in A cup
{h}`), and let `Theta_i` (`i in I`) be the automorphisms of
[[boone-instruction-twists-extend-to-base-automorphisms]]: `psi` on `G_1`
(`x -> x`, `s -> s x^-2`, `h -> h`) composed with a swap `q_j <-> q_k` and a
transvection `q_k -> u q_k v` (`u, v in G_1`) on the free factor.  Show that
there is an injective *-homomorphism `Phi : C*(B) -> prod M_n / (+) M_n` and
unitaries `U_i` in the corona with `U_i Phi U_i^* = Phi o Theta_i` for all
`i in I`.

By [[crossed-product-by-corona-inner-automorphism-is-mf]] and the tower of
[[boone-instruction-twists-extend-to-base-automorphisms]], this makes every
Boone group operator-MF with MF full group C-star algebra.

## Attempts

*Amenable base.*  For an amenable base Shulman's Corollary 35 does this
through the uniqueness of trace-preserving embeddings into the UHF algebra.
`G_1` is not amenable (it is Higman's non-residually-finite double of
`BS(1,2)` when `|A| >= 1`), so uniqueness of embeddings is unavailable and
the attack has to use the structure.

*Piecewise inner part.*  `psi` is `Ad(x^-2)` on each factor `BS(1,2)_s`, `s
in A`, and the identity on `BS(1,2)_h`.  Implementing it amounts to a corona
unitary `Y` centralizing `Phi(BS_s)` for all `s in A` and implementing
`Ad(x^2)` on `Phi(BS_h)`.  Shulman's embedding of the symmetric amalgam is
obtained by lifting an abstract representation, so it is not clear that it
carries such a `Y`; an explicit embedding of `*_<x> BS(1,2)` with a visible
factorwise structure is what is missing.

*Free part.*  With free Haar-type unitaries `V_l` for the free factor, the
swap and transvection preserve the joint distribution of `(Phi(G_1), V_l)`,
but norm-conjugacy in the corona is stronger than equality in distribution;
one needs to construct the `V_l` with the symmetry built in, for example as
`V_j = P V_k P^*` for a unitary `P` centralizing `Phi(G_1)`, and then solve
`(W P^2) V_k (W P^2)^* = Phi(u) V_k Phi(v)` for a `V_k` that stays free from
`Phi(G_1)`.  This is a concrete conjugacy problem in the corona and is
where the attack currently stops.

*Reduction to one edge (2026-08-25, later).*  By
[[boone-base-semidirect-product-is-hnn-over-free-subgroups]], after folding
the machine states into tape letters, `C*(B x| F_I)` is MF as soon as the
single HNN edge `q_1^-1 (u_i^-1 theta_i) q_1 = v_i theta_i` (`i in I`) over
the symmetric amalgam `H_1 = *_(G_1) (G_1 x|_psi Z)` is MF-safe; the
amalgam factor `G_1 x|_psi Z` is regularly MF by
[[rotman-g1-is-central-hnn-of-baumslag-solitar]].  The edge is between two
free subgroups of rank `|I|` whose bases have identical free-Haar
distribution under the regular character, so the obstruction, if any, is not
tracial.

