---
rg: 2
id: boone-higman-via-bffhz-action-image
kind: route
title: Quotient the relative automorphism group by its action kernel and take the twisted Brin-Thompson group
target: boone-higman-conjecture
requires: [boone-higman-thompson-simple-envelope, relative-automorphism-action-is-highly-transitive, bffhz-action-image-is-finitely-presented, twisted-brin-thompson-finite-presentation-criterion]
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

The one route in this region that does not pass through
`chatterji-kassabov-normal-generator-embedding`.

Let `G` be finitely generated with solvable word problem.  By
`boone-higman-thompson-simple-envelope`, applied to `G × Z`, embed
`G <= S` with `S` infinite, finitely generated, computably presented and
simple.  Fix `n >= 2` and set

    A = Aut_S(S * F_n) ,   X = Hom_S(S * F_n, S) ,   K = ker(A on X) ,
    Abar = A/K .

By `relative-automorphism-action-is-highly-transitive` the
action of `A` on `X` is highly transitive with finitely generated point
stabilizers, and the translation copy of `S` inside `A` acts freely, so
`K ∩ S = 1` and `S` embeds in `Abar`.  The induced action of `Abar` on `X` is
faithful by construction, still highly transitive — hence in particular has
finitely many orbits on pairs — and still has finitely generated point
stabilizers.

By `bffhz-action-image-is-finitely-presented`, `Abar` is finitely presented.
The three hypotheses of
`twisted-brin-thompson-finite-presentation-criterion` now hold for
`Abar` acting on `X`, so `SV_Abar` is finitely presented, and faithfulness
makes it simple.  It contains `Abar`, hence `S`, hence `G`.

## Why every prerequisite is genuinely used

The envelope theorem supplies the simple core.  The imported action analysis
supplies transitivity, stabilizers, and the freeness that keeps the core
alive in the quotient.  The open claim supplies the only missing hypothesis.
The criterion supplies the conclusion.  Removing the quotient by `K` and
working with `A` directly is not an option: faithfulness is what makes the
twisted Brin--Thompson group simple, and `A` is faithful only under a
mixed-identity-free hypothesis on `S` that the Boone--Higman--Thompson core
is not known to satisfy.

## The trap this route is most likely to be misread into

`bffhz-action-image-is-finitely-presented` is **not** the published open
question it resembles.  Belk--Fournier-Facio--Hyde--Zaremsky Question 3.2
asks the same thing for a *finitely presented* simple `G` and its payoff is
universality of twisted Brin--Thompson groups, not Boone--Higman.  Here the
core is only computably presented — because if it were finitely presented the
conjecture would already hold for that input — so this route needs strictly
more than the published question.  The distinction is recorded on the claim
node and repeated here because the two statements differ by one adjective and
that adjective is the whole problem.

## What is genuinely appealing about it anyway

`Abar` is a very large permutation group compared with `S`.  Route A and
Route B both ask a finiteness question about the envelope's lattice or its
double cosets; this one asks whether a *bigger* group can be finitely
presented than the one whose relators are infinite in number.  That is a
different kind of hope — compression by enlargement rather than by selection
— and it is the reason the route is kept despite needing more than a
published question.
