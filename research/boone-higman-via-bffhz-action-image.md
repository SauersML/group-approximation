---
rg: 2
id: boone-higman-via-bffhz-action-image
kind: route
title: Excluded universal computable-core upgrade through the relative automorphism action image
target: boone-higman-conjecture
requires: [boone-higman-thompson-simple-envelope, relative-automorphism-action-is-highly-transitive, bffhz-action-image-is-finitely-presented, twisted-brin-thompson-finite-presentation-criterion]
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
  - research/artifacts/boone-higman-relative-automorphism-fp-obstruction-2026-09-08.md
---

This conditional implication has a refuted universal prerequisite and is
not a live route. `bffhz-computable-core-fp-upgrade-is-false` supplies a
decidable simple core whose evaluation action is faithful but whose
relative automorphism group is not finitely presented. The implication
below records what the proposed prerequisite would have supplied.

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

If `bffhz-action-image-is-finitely-presented` held, `Abar` would be finitely presented.
The three hypotheses of
`twisted-brin-thompson-finite-presentation-criterion` now hold for
`Abar` acting on `X`, so `SV_Abar` is finitely presented, and faithfulness
makes it simple.  It contains `Abar`, hence `S`, hence `G`.

## Why every prerequisite is genuinely used

The envelope theorem supplies the simple core.  The imported action analysis
supplies transitivity, stabilizers, and the freeness that keeps the core
alive in the quotient. The now-refuted claim was intended to supply finite presentation.
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
core is only guaranteed computably presented — a finitely presented simple
core would already settle that input — so this route required strictly
more than the published question. That stronger assertion is now refuted.
The distinction is recorded on the claim
node and repeated here because the two statements differ by one adjective and
that adjective is the whole problem.

## Scope of the obstruction

For MIF simple cores, `relative-automorphism-fp-host-reflects-base-presentation`
shows that the faithful action image is finitely presented exactly when
the core is. A selective construction using non-MIF cores, or a different
action, remains outside this refutation. No such construction has been
supplied here, and the published finite-presentation question remains open.
