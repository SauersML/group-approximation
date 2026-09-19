---
rg: 2
id: z-fixed-support-three-elements-cannot-witness
kind: claim
title: A support-three element fixing the C3 averaging idempotent cannot witness one-sided invertibility
distinct_from:
  leavitt-rank-three-lift-has-no-one-sided-inverse: that kills one explicit support-three Leavitt lift by identifying its virtually free support subgroup; this kills every support-three unitized factor arising from the Leavitt corner, using only its fixed averaging idempotent.
  leavitt-corner-witness-has-unitized-rank-floor: that used the published rank-pair bound to leave `(3,13)` open; this eliminates the entire rank-three branch regardless of the partner's support.
  subgroup-supported-one-sided-inverse-rigidity: that is the general inverse-localization lemma; this proves that the support subgroup forced by the C3 incidence equations is amenable and hence supplies the lemma's hypothesis.
artifacts:
  - research/artifacts/leavitt-corner-small-rank-coset-classification-2026-08-21.md
---

Let `G` be any group, `H=<g>` a subgroup of order three, and
`z=sum_(h in H)[h] in F_2[G]`.  If `alpha` has support three and

```text
alpha z=z alpha=z,
```

then the support of `alpha` lies in an amenable subgroup of `G`.  Therefore,
if `alpha beta=1` for any `beta in F_2[G]`, necessarily `beta alpha=1`.

Applied to the unitization of a Leavitt corner pair, both factors fix `z`, so
neither can have support three.  The `(3,13)` profile left open by
`leavitt-corner-witness-has-unitized-rank-floor` is impossible; every corner
witness must have ordered unitized support profile at least `(5,7)`.
