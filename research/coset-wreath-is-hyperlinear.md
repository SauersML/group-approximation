---
rg: 2
id: coset-wreath-is-hyperlinear
kind: claim
title: The summit arithmetic coset wreath is hyperlinear
invalidates:
  - nonhyperlinear-coset-wreath-from-p3-collapse
  - nonhyperlinear-from-lamp-torsor-excess
artifacts:
  - research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md
distinct_from:
  hyperlinear-wreath-model: that is the Q3.4 hole asking for hyperlinear models of the KUN-THOM wreath (already known nonsofic); this is the same question for the ARITHMETIC summit wreath W_3, where nonsoficity is open, the collapse machinery lives, and the entropy ceiling constrains any model to be rigid.
  arithmetic-coset-wreath-is-not-sofic: that is the soficity question for W_3; this is the strictly weaker hyperlinearity question, and the two together feed the separation root rather than the main goal.
---

Claim (OPEN, the fork's other half, recorded per the two-sided
doctrine): `W_3` is hyperlinear.

Establishing this claim refutes the two goal routes through `W_3`
(hence the `invalidates` keys): the p = 3 collapse fails (the base lamp
is a leak) and the excess-entropy hole is false
(`coset-wreath-hyperlinearity-forces-strong-one-boundedness` then
forces `h(L(W_3)) = 0` exactly).  It is NOT a loss for the program if
it comes with `arithmetic-coset-wreath-is-not-sofic`: the pair closes
the separation root via
`separation-from-nonsofic-hyperlinear-wreath` — Pestov's Question 3.4
resolved by separation, with an explicit arithmetic witness.

What any proof must look like, per the landed constraints: the model
must realize the base lamp as a `Lambda`-central involution moved by
`pi(h)` (so `SL_3(Z)` regular-trace microstates uniformly far from
every finite-index subgroup's genuine representations — the collapse
lane's outlier sector must be NONEMPTY); and by the entropy ceiling the
construction must be RIGID: at every scale its conjugation-quotient
moduli are subexponential in `d^2` (any macroscopic surviving freedom
would instead prove non-hyperlinearity through
`nonhyperlinear-from-lamp-torsor-excess`).  The live constructive
approach is the p = 2 flat-tower program of the Lambda-exact face
(`lambda-exact-face-of-the-collapse-closes` endgame: trivial
metaplectic flux at p = 2), transported to p = 3 only if the flux
identification fails.

## Attempts

- **Flat-tower construction (the only live approach).**  The
  Lambda-exact analysis leaves exactly one enemy format at p = 2:
  flat multi-scale solenoidal towers with trivial Matsumoto flux, up to
  one trivializable cocycle.  It must still satisfy the remaining Behr
  relations and produce genuine vanishing-defect microstates for ALL of
  `W_3` (mixed lamp-group moments), which no probe has achieved; and
  the subquadratic-gauge and vanishing-tangent theorems
  (`finite-congruence-wreath-lamp-torsors-are-subquadratic-gauge`,
  `finite-wreath-relative-tangent-moduli-vanish`) show it cannot be
  reached from exact finite packets by infinitesimal deformation — it
  must be genuinely far from every finite table.
- **Permanence theorems: all blocked.**  Every wreath permanence
  theorem (Hayes-Sale, GKEP, Holt-Rees, Alekseev-Bradford) needs a
  sofic/permutational coset action, unavailable here (and for the KT
  wreath refuted); amenable-stabilizer results do not apply
  (`Lambda` has (T)).  A new permanence principle for commensurated
  Kazhdan stabilizers would be a major theorem in its own right.
