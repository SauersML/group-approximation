---
rg: 2
id: regular-character-not-mf-trace-proof
kind: route
title: Instantiate the recognition theorem at the literal group and refute its conclusion
target: regular-character-not-mf-trace
requires: [regular-character-mf-trace-implies-group-mf, literal-group-fails-mf-conventions]
artifacts:
  - GroupApproximation/Sofic/LiteralTraceConsequence.lean
---

## Why sufficient

`regular-character-mf-trace-implies-group-mf` says that a group whose regular
character is an MF trace is operator MF.  `literal-group-fails-mf-conventions`
says the literal group `E` is not, under every formalized convention including
the literal Carrion--Dadarlat--Eckhardt one.  Contraposition gives the target.

The only thing to check is that the two conventions meet, and they do: the
recognition theorem concludes `IsNormApproximable E 1`, and the two bridges
`OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one` and
`isCDEOperatorMF_iff_isOperatorMF` carry that to `IsCDEOperatorMF E`, which is
the exact predicate the non-MF theorem negates.  Both bridges need
`Countable E`, which is available as an instance.

Written out, in `LiteralTraceConsequence.lean`:

```text
intro h
refine markedGroup_finitelyPresented_sofic_nonMF.2.2 ?_
refine (isCDEOperatorMF_iff_isOperatorMF MarkedGroup).mpr ?_
refine isOperatorMF_iff_isNormApproximable_one.mpr ?_
exact isNormApproximable_of_isMFRegularCharacter MarkedGroup h
```

## Trust surface

None beyond the two prerequisites.  No literature input, no hypothesis, no
new estimate; the route is a composition and its whole content is that the
conventions line up.
