---
rg: 2
id: fournier-facio-dimension-face-holds-every-approximation
kind: claim
title: Every hyperlinear approximation of the Fournier--Facio group gives a witness on the dimension-at-infinity face
distinct_from:
  fournier-facio-dimension-at-infinity-escape-is-sharp: That is a one-generator calibration for the group of integers; this shows that the whole dimension-at-infinity face contains, after a random rotation of each block, every ordinary normalized-HS approximation of the Fournier--Facio group, with trivial block action.
  fournier-facio-hyperlinear-iff-singular-near: That is the equivalence between hyperlinearity and a purely singular free near state; this locates the witnesses coming from actual approximations on one explicit face of the survivor dichotomy.
  fournier-facio-block-dimension-escapes-every-charge-cutoff: That is the necessary escape law for common-block witnesses; this shows every ordinary approximation already satisfies it, so the law excludes nothing an approximation would provide.
artifacts:
  - research/artifacts/fournier-facio-hyperlinearity-survivor-audit-2026-09-11.md
---

**ESTABLISHED CALIBRATION.**  Suppose `phi_n:G -> U(d_n)` is a
normalized-Hilbert--Schmidt approximation of the Fournier--Facio group: for
all `g,h`, `||phi_n(gh)-phi_n(g)phi_n(h)||_2 -> 0` and `tr(phi_n(g)) -> 0`
for `g!=1`.  Then there are unitaries `W_n in U(d_n)` and a purely singular
probability charge `mu` on `X=disjoint_union_n [d_n]` such that

```text
pi(g) = direct_sum_n W_n^* phi_n(g) W_n                       (DF1)
```

is a Kahl--Schneider essentially free amenable near representation.  Its
generator support components are finite, contained in the blocks `[d_n]`,
and of sizes escaping every cutoff in charge.  The induced block near action
is the trivial action.

Consequently every witness produced by an actual hyperlinear approximation
lies on face (S2) of the survivor audit, with every group element fixing every
block.  The recorded (S2) laws cost such a witness nothing beyond the regular
character:

- `fournier-facio-block-dimension-escapes-every-charge-cutoff`;
- `fournier-facio-fixed-block-spectrum-escapes`;
- `fournier-facio-fixed-block-actor-is-charge-haar`.

So no combinatorial fence on face (S2) can close the positive branch without
proving nonhyperlinearity outright.  The genuinely exotic face is (S1),
infinite support components, which ordinary approximations never use.
Conversely, a universal no-go has to act on face (S2), that is, on ordinary
normalized-HS approximations.

Proof: `fournier-facio-dimension-face-calibration-proof`.
