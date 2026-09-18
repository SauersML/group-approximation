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

**OPEN** as stated (demoted 2026-09-18; see Attempts). Items 1-4 and the "if" half of item 5
are proved. The "only if" half of item 5, the Dichotomy, rests on an unproved and uncited
injectivity of `S -> (U/I)^x` for an arbitrary witness; that is now the hole
`sandwich-witness-quotients-embed-the-perfect-core`, required by the route.

Let `R` be a finitely presented unital associative ring.

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

## Attempts

- 2026-09-18 (adversarial referee pass, outcome refuted as stated, verdict f3ec0e29): **Step 8
  asserts an injectivity it neither proves nor cites.** Referee's reason, verbatim:
  - "Items 1-4 of the claim and Steps 1-7 of the route are correct (I checked the corner
    isomorphism M_4(R) = eRe, rho(g) = 1 + x_1 y_2, the relation (-y_1)(-x_1 y_2)(x_2) = 1,
    surjectivity theta(p)(x_1 r y_2)theta(q) = -r, the ring Tietze argument for finite generation of
    ker theta, the summand argument R = R + P, P^m = R + Q, R = R + R^k + Q^k, and Step 7's unit
    argument; all three prerequisites are ESTABLISHED and are applied with matching hypotheses,
    n = 4 >= 4, n >= 2, n >= 3). The failure is Step 8 of
    research/non-directly-finite-ring-hosts-are-sandwich-ring-quotients-proof.md line 138, which
    proves the 'only if' half of item 5 (the Dichotomy, part of the ESTABLISHED statement). It
    asserts flatly 'S -> R^x is injective' for an arbitrary witness R = U/I, with no proof and no
    citation, and the route's requires list ([projective-elementary-fp-kernel-criterion,
    perfect-unit-subgroups-embed-in-elementary-groups,
    projective-elementary-simplicity-forces-simple-ring]) contains nothing that yields it. It is not
    automatic: S <= H <= T maps to (U/I)^x and its kernel, being normal in the simple group S, is 1
    or S; the relation p(1-g)q = 1 only forces the image of g to differ from 1, so if g is not in S
    nothing stops the entire core S from collapsing to 1 in (U/I)^x, and then the witness ring is
    not an (NDF) host and the only-if direction fails. The graph's own lemma for this,
    ck-envelope-level-ideal-screen (ESTABLISHED), does not close it verbatim: its hypothesis is 'let
    S be an infinite simple group, choose 1 != g in S', and its proof of part (3) needs g in the
    two-sided ideal of Z[S] generated by 1-s, i.e. it needs g in S, whereas
    ck-sandwich-ring-has-fp-projective-simple-quotient only posits '1 != g in H' with H possibly
    strictly larger than S. So the needed import is both uncited and, as stated, quantified over a
    strictly stronger hypothesis than the hole supplies. A secondary (repairable, non-decisive)
    slip: item 2 drops the 'nontrivial' hypothesis of
    projective-elementary-simplicity-forces-simple-ring, though nontriviality does follow since
    E_4(R) is perfect and e_12(1) != 1. The claim asserts no computation, so step 4 of the review
    was vacuous. Verdict posted as refuted (f3ec0e29)."
  - **The exact step that fails.** Step 8 of the route, the "only if" half: "`S -> R^x` is
    injective".
  - **Demotion.** The missing statement is now
    `sandwich-witness-quotients-embed-the-perfect-core` (OPEN), added to the route's `requires:`.
    The proof file is kept: Steps 1-7, items 1-4 and the "if" half all stand.
