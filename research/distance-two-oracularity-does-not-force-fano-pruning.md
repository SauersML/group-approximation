---
rg: 2
id: distance-two-oracularity-does-not-force-fano-pruning
kind: claim
title: Even classical distance-two oracularity can retain every point of every Fano line
distinct_from:
  extreme-traces-and-local-pruning-do-not-select-fano-caps: that gives abstract factor and symmetry countermodels; this is a finite 3SAT-10-format incidence counterexample with globally consistent neighborhood links.
  culf-mastel-rstar-fixed-language-gap-is-published: that proves only ordinary contextwise commutation for the hard family; this shows that adding distance-two commutation alone would still not imply cap support.
---

**ESTABLISHED COUNTEREXAMPLE TO THE STRUCTURAL IMPLICATION.**  In the usual
weighted-CSP/multiset convention, take ten labeled copies of the same
positive clause

```text
x OR y OR z.                                                (DTO1)
```

Each variable occurs exactly ten times, so this is a 3SAT-10 instance.  Its
ten constraint neighborhoods form a clique.  Use the classical perfect
strategy obtained by choosing uniformly one of the seven satisfying
assignments and returning that same assignment to every clause copy.

All measurement algebras commute globally, hence satisfy every proposed
distance-two or `2`-oracular commutation requirement.  Nevertheless every
local support is the full seven-point one-ghost relation.  For every context
`c`, every `a in R_c`, and every neighbor, choosing the same assignment `a`
gives a globally consistent tuple in `Link(c,a)`.  Thus no atom is pruned,
and every Fano line survives.

The obstruction persists through a pp reduction to `R_*`.  If all positive
source assignments in this full support admitted witnesses whose target
occurrence ranges were Fano caps, then
`fano-cap-witness-sections-force-source-affine-safety` would imply

```text
Aff(R_OR) subseteq R_OR.                                    (DTO2)
```

But the seven satisfying assignments of a positive 3-clause are the seven
nonzero points of `F_2^3`, whose affine hull is all of `F_2^3` and contains
the forbidden `000`.  Hence some lifted target context must retain a Fano
line.  This argument is classical, so adding still more commutation cannot
repair it.

If a definition of 3SAT-10 forbids repeated labeled constraints, `(DTO1)`
should be read only as a counterexample in the standard CSP multiset format;
the same logical counterexample is given directly by equality-linked copies
of the full `R_*` relation.  Either version proves that distance-two
oracularity needs the independent line-hitting condition `(FEL2)`.

