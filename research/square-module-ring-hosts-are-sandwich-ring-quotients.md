---
rg: 2
id: square-module-ring-hosts-are-sandwich-ring-quotients
kind: claim
title: Every finitely presented ring isomorphic to its square with finitely presented simple projective elementary group is a finitely generated quotient of a sandwich ring over its own elementary group
distinct_from:
  ck-sandwich-ring-has-fp-projective-simple-quotient: that is the open existence question for a specific core S; this is an established realisation lemma showing that any square-module ring host of S already is a witness, with T = H = E_4(R) and g = e_12(1).
  ck-maximal-kernel-four-regimes: that shows a witness in the congruence regime must be a finitely generated ideal with finitely presented simple projective quotient; this is the converse construction, turning a ring host into such an ideal of a sandwich ring.
  universal-sandwich-ring-is-finitely-presented-and-injective: that proves finite presentation and injectivity of the universal sandwich extension; this maps a sandwich ring ONTO a given host and identifies the quotient.
  decidable-group-ring-has-fp-projective-simple-host: that is the open ring-host existence premise for group rings; this is an established transfer lemma from ring hosts with R = R^2 to the sandwich-ring hole.
  non-ibn-ring-el-n-full-mf-radical-above-module-rank: that uses R^m = R^(m+d) to kill MF quotients; this uses R = R^2 to identify all elementary groups E_n(R) with E_4(R) and to realise R as a sandwich quotient.
---

**ESTABLISHED.** Let `R` be a finitely presented unital associative ring such
that `R_R ≅ R_R ⊕ R_R` as right modules.

1. **Rank independence.** For all `m, n >= 2` there is a group isomorphism
   `E_m(R) ≅ E_n(R)`. In particular `PE_m(R) ≅ PE_n(R)`, and `E_n(R)` is
   finitely presented (simple) for one `n >= 2` iff it is for all.
2. **Sandwich realisation.** Suppose `PE_4(R)` is finitely presented. Put
   `T = H = E_4(R)`, `g = e_12(1)` and

       U = Z[T]<p,q> / (p(1-g)q - 1).

   Then `T` is finitely presented and perfect (so `H <= [T,T]`), and the
   inclusion `T <= GL_4(R)` extends to a surjective ring homomorphism
   `U ->> M_4(R)` whose kernel `I` is a finitely generated two-sided ideal.
   Moreover `U/I ≅ M_4(R) ≅ R` as rings, so `PE_4(U/I) ≅ PE_4(R)`.
3. **Consequence for the hole.** If in addition `PE_4(R)` is simple and `S` is
   a perfect subgroup of `R^x` (for instance an infinite simple group), then
   `S` embeds in `H = E_4(R)` and the triple `(H, T, g)` with the ideal `I`
   witnesses [[ck-sandwich-ring-has-fp-projective-simple-quotient]] for `S`.

So a witness of that hole exists for `S` as soon as `S` sits in the units of a
finitely presented ring `R ≅ R^2` whose rank-four projective elementary group
is finitely presented and simple. None of the Clapham or derived-subgroup data
of [[boone-higman-via-ck-maximal-kernel]] is used: the marking is the host's
own elementary group.

DERIVATION
[[square-module-ring-hosts-are-sandwich-ring-quotients-proof]]

## What it shows about the hole

Combined with Step 3 of [[ck-maximal-kernel-four-regimes]], the hole for `S` is
sandwiched between two ring-host statements.
- **Sufficient (this claim):** some finitely presented `R ≅ R^2` has `S <= R^x`
  and `PE_4(R)` finitely presented and simple.
- **Necessary (the four-regimes claim and the level screen):** some finitely
  presented simple ring `R = U/I` has `S -> R^x` injective,
  `p(1-g)q = 1` for one `1 != g in S`, and `PE_4(R)` finitely presented and
  simple.

The only gap between the two is the square-module condition `R ≅ R^2`. The
sandwich ring `U` imposes no obstruction of its own. Any construction of a
square-module ring host is a witness.
