---
rg: 2
id: residual-finiteness-of-enumerated-presentations-is-pi3-complete
kind: claim
title: Residual finiteness is Pi-zero-three complete for recursively enumerated presentations, one level above local embeddability
artifacts:
  - GroupApproximation/Computability/RFPresentationPi02.lean
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  lef-recognition-has-a-pi2-upper-bound: that places LEF at the second level; this shows residual finiteness sits strictly one level higher on the same syntax, so the two properties that coincide for finitely presented groups are separated by the arithmetical hierarchy on recursive presentations.
  mf-recognition-two-generator-recursive-is-pi2-complete: that is a second-level completeness theorem; this is a third-level one, with a different mechanism (profinite closure of a subgroup of a free group) and a different index set.
  second-level-rice-theorem-for-local-approximation-properties: that gives Pi-zero-two hardness for every hereditary property containing the residually finite groups, including residual finiteness itself; this climbs one more level, which no local approximation property can do because they are all Pi-zero-two.
---

ESTABLISHED.  For the standard coding of countably generated recursively
enumerated presentations (`EnumeratedPresentationCodes.PresentationCode`),

```text
RF_enum     is Pi^0_3-complete,
NONRF_enum  is Sigma^0_3-complete.                                    (RF1)
```

For finitely generated recursive presentations `RF_rec` is `Pi^0_3` and
`Pi^0_2`-hard, and for finite presentations `RF_fp` is `Pi^0_2` and
`Sigma^0_1`-hard.

**Contrast.**  On the same syntax LEF is `Pi^0_2`
([[lef-recognition-has-a-pi2-upper-bound]]), so residual finiteness and
local embeddability into finite groups, which coincide for finitely
presented groups, are separated by one quantifier alternation on recursive
presentations.  The extra alternation is exactly "one finite quotient kills
*all* the enumerated relators", a `Pi^0_1` condition inside the certificate.

## The hardness family

For a c.e. index `c` let `a_j = b^j a b^-j` in `F = F(a, b)`, `j >= 0`, and

```text
H_c = < a, b, s | [s, a_j] = 1  for  j < |W_c| >,                     (RF2)
```

the `j`-th relator being emitted when the `(j+1)`-st element of `W_c`
appears.  Then

```text
W_c finite    ==>  H_c is residually finite,
W_c infinite  ==>  H_c is not residually finite,                       (RF3)
```

and for a `Pi^0_3`-complete set `{e : for all x, W_g(e,x) finite}` the
countable free product `G_e = *_x H_g(e,x)` is residually finite iff `e`
is in the set.

## Sharpening

The finitely generated case is settled at three generators by
[[residual-finiteness-three-generator-recursive-is-pi3-complete]], through
the exact criterion
[[centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed]] and
the dyadic index sets of [[index-set-profinitely-closed-is-pi3-complete]];
the countable free product above is then no longer needed.  Two generators, the
optimum, is [[residual-finiteness-two-generator-recursive-is-pi3-complete]]
via the shift right-angled Artin family
[[shift-raag-family-is-rf-iff-symmetrized-index-set-closed]]; and
`Pi^0_2`-completeness of `RF_fp` is the residually finite Higman problem,
open in the literature.

**Machine-checked (finite presentations).**  `Computability/RFPresentationPi02.pi02_residuallyFinite` is the `Pi^0_2` membership of `RF_fp` and `rf_fp_strict_position` the placement `Pi^0_2 \ Pi^0_1` / `Sigma^0_2 \ Sigma^0_1`, with the Markov data seeded by the finitely presented nonsofic group.
