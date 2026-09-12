---
rg: 2
id: boone-instruction-twists-extend-to-base-automorphisms
kind: claim
title: Every instruction-letter twist of the Boone group is the restriction of an automorphism of its base
distinct_from:
  boone-base-group-two-generator-one-relator: that identifies the base of Simpson's modular-machine group; this concerns Rotman's Turing-machine Boone group and the automorphism structure of its instruction letters.
  asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope: that is the general embedding lemma; this exhibits the inner envelope for one specific group and derives that the Boone group lies in a central-HNN tower over a free-by-base semidirect product.
---

ESTABLISHED.  Take Rotman's Boone group of a Turing machine `T` in the
presentation of Marchand's notes (following Rotman, *An introduction to the
theory of groups*, Ch. 12): generators `Q cup A cup {q, h} cup {r_i : i in I}
cup {x, t, k}` and relations

```text
(B1)  s^-1 x s = x^2                         (s in A cup {h}),
(B2)  s^-1 r_i s = x r_i x                   (s in A, i in I),
(B3)  r_i^-1 (abar_i q_j(i) beta_i) r_i = gbar_i q_k(i) delta_i,
(B4)  [t, r_i] = [t, x] = [k, r_i] = [k, x] = [k, q^-1 t q] = 1.
```

Its HNN tower is `G_1 = < x, A, h | (B1) >` (the symmetric amalgam of copies
of `BS(1,2)` over `<x>`), `B = G_1 * F(Q cup {q})`, `G_2 = B *_(r_i)` with
associated subgroups

```text
A_i = < s x (s in A), abar_i q_j beta_i >,   B_i = < s x^-1 (s in A), gbar_i q_k delta_i >,
r_i^-1 a r_i = phi_i(a),     phi_i(s x) = s x^-1,   phi_i(abar q_j beta) = gbar q_k delta,
```

(`(B2)` is `r_i^-1 (s x) r_i = s x^-1`), then `G_3 = < G_2, t | [t, <r_i, x>] = 1 >`
and `G_nb(T) = < G_3, k | [k, <r_i, x, q^-1 t q>] = 1 >`.

**Claim.**  For every `i` there is an automorphism `Theta_i` of `B` with
`phi_i = Theta_i|_(A_i)`.  Consequently, with `D = B x| F_I` the semidirect
product of `B` by the free group on letters `theta_i` acting through
`Theta_i`,

```text
G_nb(T)  <=  < < < D, z_i | [z_i, A_i] = 1 >, t | [t, <r_i,x>] = 1 >, k | [k, <r_i,x,q^-1tq>] = 1 >,
r_i -> z_i theta_i,                                                    (BT1)
```

a three-stage tower of central HNN extensions over `D`.  In particular the
Boone group is operator-MF, and even has MF full group C-star algebra, as
soon as `C*(B x| F_I)` is MF.

## Proof

*The automorphism.*  Let `psi` be the endomorphism of `G_1` with `psi(x) =
x`, `psi(s) = s x^-2` for `s in A`, `psi(h) = h`.  It respects `(B1)`:
`(s x^-2)^-1 x (s x^-2) = x^2 (s^-1 x s) x^-2 = x^2`, and `s -> s x^2` is an
inverse, so `psi` is an automorphism, with `psi(s x) = s x^-1`.  Extend
`psi` by the identity on the free factor `F(Q cup {q})` to an automorphism
`Psi` of `B`.  Put `u = psi(abar_i)^-1 gbar_i` and `v = delta_i
psi(beta_i)^-1`, elements of `G_1`, and let `j = j(i)`, `k = k(i)`.  Define
`Theta_i = beta_(k) o alpha o Psi`, where `alpha` swaps the free generators
`q_j` and `q_k` (identity if `j = k`) and `beta_(k)` sends `q_k` to `u q_k v`
and fixes all other generators.  Each factor is an automorphism of the free
product (`beta_(k)` has inverse `q_k -> u^-1 q_k v^-1`), so `Theta_i` is.
Then `Theta_i(s x) = psi(s x) = s x^-1`, and

```text
Theta_i(abar_i q_j beta_i) = psi(abar_i) u q_k v psi(beta_i) = gbar_i q_k delta_i.
```

Since `A_i` is free on the displayed generators (Rotman), `phi_i` is
determined by its values on them, so `phi_i = Theta_i|_(A_i)`.

*The tower.*  In `D`, `theta_i^-1 b theta_i = Theta_i(b)`, so `phi_i` is
inner in `D`.  By [[asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope]]
(the multiple-stable-letter version has the same Britton proof), `G_2 = B
*_(phi_i) <= D *_(phi_i) = < D, z_i | [z_i, A_i] = 1 >` with `r_i = z_i
theta_i`.  The letters `t` and `k` are central over subgroups of `G_2`, and
a central HNN extension of a subgroup embeds in the central HNN extension of
the overgroup over the same subgroup (Britton).  This gives `(BT1)`.

*MF.*  The full group C-star algebra of a central HNN extension of a group
is the universal C-star HNN extension of the full algebra over the full
algebra of the centralized subgroup (same universal property).  If `C*(D)`
is MF, Shulman's central-HNN theorem (arXiv:2603.13564, Theorem 25) applied
three times makes the full algebra of the tower MF; `G_nb(T)` is a subgroup,
and full algebras of subgroups embed.

## What it changes

The Boone group's own MF-ness, which any Aanderaa-style compiler needs on
its positive branch, is reduced to `C*(B x| F_I)` with `B = (*_<x> BS(1,2))
* F(Q cup {q})`, i.e. to implementing finitely many explicit automorphisms of
`B` by corona unitaries in one embedding; see
[[crossed-product-by-corona-inner-automorphism-is-mf]] and
[[boone-base-has-corona-inner-instruction-automorphisms]].
