---
rg: 2
id: openai-expander-matching-criterion
kind: claim
title: The expander-matching criterion - a compressed Kazhdan pair with a commuting factor forces that factor to be LEF
distinct_from:
  one-sided-compression-nonsofic-criterion: That is this development's own formalized bridge, stated on a `CompressionSetup` and concluding nonsoficity of the ambient group from a non-LEF witness; this is the chapter's Proposition 2.3, stated on a subgroup triple and concluding LEF of the commuting factor. They are the same mechanism discovered twice, and neither is derived from the other here.
  kun-expander-decomposition-formalized: That is the first input, which produces a union of expanders from property (T) and concludes nothing about any group; this is the criterion built on top of it, and its content is the passage from many components to one.
  kun-thom-expander-centralizer-formalized: That is the second input, which consumes a single expander on the whole approximation set; this is what manufactures such an approximation from data that property (T) alone supplies.
  openai-leavitt-unit-nonsofic: That is the theorem about one explicit group; this is the group-theoretic criterion behind it, quantified over every compressing triple and mentioning no ring.
artifacts:
  - c1168433:official/counterexample.tex
  - c1168433:official/reasoning.tex
---

ESTABLISHED.  This is Proposition 2.3 of the OpenAI nonsofic chapter, the
step that made the first nonsofic group possible.

> Let `Gamma <= G` be infinite finitely generated groups with property (T).
> Suppose that
>
>     G = <Gamma, t_1, ..., t_m>,   t_i Gamma t_i^(-1) <= Gamma   (1 <= i <= m),  m >= 1.
>
> If a finitely generated subgroup `J <= G` satisfies
>
>     [Gamma, J] = 1,   Gamma cap J = {1},   t_1 J t_1^(-1) <= Gamma,
>
> then soficity of `G` implies that `J` is LEF.

The hypotheses say that `Gamma x J` sits inside `G` **and** that one single
conjugation carries both commuting factors into `Gamma`:
`t_1 (Gamma x J) t_1^(-1) = (t_1 Gamma t_1^(-1)) x (t_1 J t_1^(-1)) <= Gamma`.
That extra nesting is what a bare direct product does not have, and the
chapter shows it is exactly what is missing.

## Why the nesting is not decoration

The obvious weakening is false.  Take `Lambda = SL_3(Z)` and
`B = BS(2,3) = <a,b | a b^2 a^(-1) = b^3>`.  Then `Lambda` has (T) and is
residually finite, hence sofic; `B` is finitely presented and sofic but not
residually finite, hence not LEF; and `Lambda x B` is sofic.  So the expanding
`Lambda`-components of a sofic approximation cannot on their own force their
commuting factor to be LEF.  Any proof must produce **one** expander, and the
compressors are what produce it.

## Version trap

The chapter exists in two versions with the same proposition numbers and
different hypotheses; see [[openai-leavitt-unit-nonsofic]] for the table.  The
statement above is the original.  In the current version property (T) is asked
of `Gamma` only, and the conclusion is drawn from an explicit expanding-
approximation hypothesis rather than from bare soficity, with (T) of `G` used
only to supply that hypothesis.  Both versions support the Leavitt
application, and both give the criterion the same proof; cite the current one.

## What this repository can say about it

More than a reader normally can.  The same bridge is formalized here as
[[one-sided-compression-nonsofic-criterion]] and kernel-checked
(`Criterion/CriterionAssembly.not_isSofic_of_not_isLEF`), against the same two
external inputs, both of which are also proved here rather than quoted.  The
two statements are not literally interchangeable -- ours is packaged as a
`CompressionSetup` and returns nonsoficity, theirs is packaged as a subgroup
triple and returns LEF -- but the mechanism is the same one, and the step that
carries the whole argument is the same step.  That is why this node is
established rather than parked as an external announcement.
