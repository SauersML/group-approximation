---
rg: 2
id: non-directly-finite-ring-hosts-are-sandwich-ring-quotients
kind: claim
title: Every finitely presented ring that is not directly finite and has finitely presented simple rank-four projective elementary group is itself a finitely generated quotient of a sandwich ring
distinct_from:
  square-module-ring-hosts-are-sandwich-ring-quotients: that needs R = R^2 and maps the sandwich ring onto M_4(R), identified with R; this needs only that R^4 is a direct summand of R (automatic for a simple ring that is not directly finite) and maps the sandwich ring onto R itself through a corner embedding, with no rank independence.
  square-module-elementary-centre-is-central-units: that computes the centre of E_n(R) for R = R^d and forces a finite centre field; this realisation lemma assumes no module isomorphism R = R^d, so it does not import that centre restriction.
  ck-sandwich-ring-has-fp-projective-simple-quotient: that is the open existence question; this is an established transfer lemma which reduces it to the non-directly-finite host problem plus the directly finite witness case.
  stably-infinite-ring-elementary-groups-have-no-mf-quotient: that uses non-finiteness of R to kill MF quotients of elementary groups; this uses it to embed GL_4(R) in the units of R and realise R as a sandwich quotient.
  ck-maximal-kernel-four-regimes: that shows a congruence-regime witness is a finitely generated ideal with fp simple projective quotient; this is a converse construction from a ring host.
---

**ESTABLISHED.** Let `R` be a finitely presented unital associative ring.

1. **Corner marking.** Suppose there are `x_1, ..., x_4, y_1, ..., y_4 in R`
   with `y_i x_j = δ_ij`, which says that `R_R^4` is a direct summand of `R_R`.
   Suppose also that `PE_4(R)` is finitely presented. Put `T = H = E_4(R)`,
   `g = e_12(1)` and

       U = Z[T]<p,q> / (p(1-g)q - 1).

   Then `T` is finitely presented and perfect, and there is a surjective ring
   homomorphism `U ->> R` (onto `R` itself, not onto `M_4(R)`) that is
   injective on `T`. Its kernel `I` is a finitely generated two-sided ideal.
   So `U/I ≅ R` and `PE_4(U/I) ≅ PE_4(R)`.
2. **Simple rings.** If `R` is a simple ring that is not directly finite
   (some `ab = 1 != ba`), then `R_R^k` is a direct summand of `R_R` for every
   `k >= 1`. So the hypothesis of 1 holds. If `PE_4(R)` is simple, then `R` is
   simple by [[projective-elementary-simplicity-forces-simple-ring]].
3. **Consequence for the hole.** Let `R` be finitely presented and not directly
   finite, with `PE_4(R)` finitely presented and simple and a perfect subgroup
   `S <= R^x`. Then `(H, T, g, I)` from 1 witnesses
   [[ck-sandwich-ring-has-fp-projective-simple-quotient]] for `S`.
4. **Directly finite witnesses.** Let `R` be a directly finite ring with
   `p(1-g)q = 1`. Then `p`, `q` and `1-g` are all units of `R`.
5. **Dichotomy.** For a perfect core `S`, the hole holds if and only if at
   least one of the following holds.
   - (NDF) Some finitely presented ring `R` that is not directly finite has
     `S <= R^x` and `PE_4(R)` finitely presented and simple.
   - (DF) Some witness ring `U/I` is directly finite. By 4, `1-g` is then a
     unit of `U/I`, where `g in H` is the marked element.

DERIVATION
[[non-directly-finite-ring-hosts-are-sandwich-ring-quotients-proof]]

## What it changes

Attempt 3 of [[ck-sandwich-ring-has-fp-projective-simple-quotient]] bounded the
hole by the square-module host condition `R ≅ R^2`. That condition is replaced
by the weaker condition "not directly finite". The remaining gap is the
directly finite witnesses.

**What is not imported.** The square-module restrictions of
[[square-module-elementary-centre-is-central-units]] need `R ≅ R^d`: a finite
centre field, and `K_1` detecting no scalars. They do not transfer to (NDF).
A properly infinite ring with `[1_R]` of infinite order in `K_0` is not
excluded by that argument.

**What is imported.** The NDF branch still inherits the obstruction of
[[stably-infinite-ring-elementary-groups-have-no-mf-quotient]]:
`E_N(R)` has no MF quotients.
