---
rg: 2
id: amenable-implies-operator-mf-citation
kind: route
title: Tikuisis--White--Winter quasidiagonality gives operator-MF models for every countable amenable group
target: amenable-implies-operator-mf
requires: []
artifacts:
  - non_mf_groups_exist.tex
---

# Literature import: amenable groups are MF

This is not a new theorem.  The node was open only because the source had not
been read and bound to a Cairn route.

The exact statement needed here appears explicitly as **Theorem 2.3,
"Amenable groups are MF"**, in Christopher Schafhauser, *Finite dimensional
approximations of certain amalgamated free products of groups*,
Groups Geom. Dyn. 20 (2026), 607--615 (arXiv:2306.02498).  Schafhauser points
back to Tikuisis--White--Winter, *Quasidiagonality of nuclear C*-algebras*,
Ann. of Math. 185 (2017), Theorem A / Corollary C (arXiv:1509.08318).
The latter proves that faithful traces on separable nuclear UCT C*-algebras are
quasidiagonal and, as a stated consequence, confirms Rosenberg's conjecture
for discrete amenable groups.

## Match to this repository's convention

There **is** a convention wrinkle, but it points in the safe direction.
Schafhauser's Definition 1.1 uses a stronger group-MF notion: in addition to
operator-norm asymptotic multiplicativity/separation, his models control the
regular character and reduced norm.  The repository uses the weaker
Carrión--Dadarlat--Eckhardt operator-MF convention.  Therefore Schafhauser's
Theorem 2.3 implies the present claim immediately by forgetting the extra
trace/reduced-norm control; no converse identification of the two conventions
is being assumed.

For completeness, the standard C*-algebra route is:

1. Reduce to countable `G` (already the hypothesis of this claim).
2. If `G` is amenable, `C*_r(G)` is nuclear; the canonical regular trace is
   faithful, and the amenable-group UCT input puts it in the class to which
   Tikuisis--White--Winter applies.
3. Their theorem makes that trace quasidiagonal: on every finite subset there
   are matrix-valued completely positive contractions which are
   approximately multiplicative in **operator norm** and approximately
   trace-preserving.
4. Restrict those maps to the canonical group unitaries and polar-correct on
   the finite window.  One obtains unitary local models with operator-norm
   multiplicative defect tending to zero.  The regular trace is zero on every
   nonidentity group element, so the same trace approximation separates every
   fixed `g != 1`; equivalently one gets a faithful norm-corona embedding.

This is exactly the implication used in the manuscript's sharpness paragraph.
The route therefore establishes [[amenable-implies-operator-mf]] and, through
`cyclic-base-sharpness-proof`, closes [[cyclic-base-sharpness]].

## Source check

Sources were read on 2026-08-17 rather than copied from the repository's
attribution.  Schafhauser's printed Theorem 2.3 states the group conclusion
verbatim and its proof identifies Tikuisis--White--Winter Corollary C / Theorem
A as the quasidiagonality input.  Tikuisis--White--Winter's abstract independently
states both the faithful-trace theorem and the amenable-group consequence.
