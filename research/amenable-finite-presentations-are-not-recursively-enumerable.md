---
rg: 2
id: amenable-finite-presentations-are-not-recursively-enumerable
kind: claim
title: No algorithm enumerates exactly the finite presentations of amenable groups
distinct_from:
  amenability-of-finite-presentations-arithmetical-position: that is the established placement in Pi-zero-two minus Pi-zero-one; this is the open exclusion from Sigma-zero-one, the half of the first level that placement does not reach.
  amenability-of-finite-presentations-is-pi2-complete: that is the completeness root; this is a strictly weaker consequence, which also follows from an answer to Gromov's Følner-function question that says nothing about completeness.
---

**OPEN.** The set `AMENABLE_fp` of finite presentation codes of amenable groups
is not recursively enumerable.

**Status of the first level.**
- `amenability-of-finite-presentations-arithmetical-position` gives
  `AMENABLE_fp in Pi^0_2 \ Pi^0_1`, through Adian--Rabin.
- This claim adds `AMENABLE_fp notin Sigma^0_1`, so `AMENABLE_fp` would lie
  outside both halves of the first level.

**A consequence for provability.** Let `Th` be any recursively axiomatized theory
that proves only true amenability statements, for example ZFC under that
soundness hypothesis. If this claim holds, some finitely presented amenable
group has amenability not provable in `Th`. Indeed, if every such statement were
provable, then

```text
AMENABLE_fp = { P : Th proves "P is amenable" },                       (NRE1)
```

which is recursively enumerable. That is the "enticing possibility" at the end
of Gromov's question, quoted in
`recursive-amenable-classes-have-uniform-folner-bounds`. For non-amenability the
corresponding statement is already unconditional, since
`NONAMENABLE_fp` is not recursively enumerable by the same placement node.

**Two routes into it.**
- `amenable-fp-not-re-from-pi1-hardness`: from
  `amenability-of-finite-presentations-is-pi1-hard`, itself implied by the
  completeness root.
- `amenable-fp-not-re-from-unbounded-folner-functions`: from the negative answer
  to Gromov's question (`folner-functions-of-fp-amenable-groups-have-no-recursive-bound`),
  through Cavaleri's uniform bound. This route needs no reduction from a
  complete set at all, only one hard amenable group per recursive bound.

## Attempts

1. **Compare the settled neighbours.**
   - *Operator MF* on finite presentations is `Pi^0_2`-complete
     (`mf-recognition-finite-presentations-is-pi2-complete`), so `MF_fp` is not
     recursively enumerable. The compiler used there has a non-amenable positive
     branch and cannot be reused.
   - *Kazhdan's property (T)* is `Sigma^0_1`-complete
     (`kazhdan-property-t-of-finite-presentations-is-sigma1-complete`), so it
     *is* recursively enumerable.

   Both behaviours occur among classical properties, and neither settles this
   claim.
2. **Enumerate certified constructions.** Every c.e. family of amenability
   certificates is a proper subclass unless this claim fails. Examples are finite
   graph-of-groups assemblies with certified amenable data
   (`finite-graphs-of-amenable-groups-have-sigma1-locus`) and presentations
   Tietze-equivalent to an explicit list. *Dies as a disproof strategy.* A
   disproof would need a single c.e. certificate system complete for all
   finitely presented amenable groups. For such a system, Corollary 3.6 of
   Cavaleri would give a universal recursive Følner bound, a positive answer to
   Gromov's question.
