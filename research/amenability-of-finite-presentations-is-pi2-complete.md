---
rg: 2
id: amenability-of-finite-presentations-is-pi2-complete
kind: claim
root: true
title: Amenability of finitely presented groups is Pi-zero-two complete
distinct_from:
  amenability-of-finite-presentations-arithmetical-position: that is the unconditional strict-interval placement; this is the completeness statement, which needs a Pi-zero-two hard family of finite presentations with amenable positive branch.
  sofic-recognition-finite-presentations-is-pi2-complete: that needs a sofic-safe compiler; here the known general Higman constructions introduce free subgroups, while no general amenability-preserving embedding theorem is known.
---

OPEN.  `AMENABLE_fp` is `Pi^0_2`-complete, i.e. there is a computable map
from `INF` (or `TOT`) to finite presentations whose group is amenable on
the positive side and non-amenable on the negative side.

## Why the standard route is closed

The recursive total branch used here is `L=Z wr Z`.  Its
finite-presentation interface is directional by
[[lamplighter-fp-amenable-interface-is-directional]]: `L` embeds in the
explicit finitely presented metabelian Baumslag--Remeslennikov group, so the
positive seed does have an amenable finitely presented ambient; but the
Bieri--Strebel theorem forces every finitely presented cover of `L` to
contain `F_2`.  Thus quotient, cover, and retraction compilers are
impossible, while a nonuniform positive embedding exists.

Known general Higman HNN towers embed recursive branches but contain
`F_2` even on the total side.  No general amenability-preserving Higman
theorem is known; its existence is an open problem.  The missing object
here is more specific: a uniform conditional embedding that specializes to
an amenable finite presentation on the total branch and retains the
incomplete branch's `F_2`.

Finite-equation and finitely generated-subgroup switches cannot bridge the
gap by [[finitely-generated-centralizer-switches-are-sigma1]]: their
positive events have finite derivation certificates and are
`Sigma^0_1`, even inside a finitely presented solvable group with
undecidable word problem.  The broader theorem
[[genuine-hnn-switches-over-amenable-bases-are-sigma1]] closes every genuine
one-edge HNN switch over an amenable base: the amenable cases are exactly the
two ascending cases, again a `Sigma^0_1` event, while noninjective
endomorphism mapping tori are always amenable.  A successful construction
must propagate a genuinely infinite table through a non-genuine stable
kernel from finitely many relators.


The stronger
[[finite-graphs-of-amenable-groups-have-sigma1-locus]] closes every finite
graph-of-groups compiler with amenable finitely presented vertices and
finitely generated edges. After collapses, the only amenable cases are an
amenable vertex, an ascending loop, or the index-two line case, all witnessed
by finite derivations. Thus adding finitely many Bass--Serre rows, branches,
or stable letters cannot raise the amenable locus from `Sigma^0_1` to
`Pi^0_2`. A successful construction cannot be a finite graph of amenable
simulators.

## What a proof would need

A directly finitely presented family, presumably inside a class of
finitely presented amenable groups with undecidable word problem
([[finitely-presented-amenable-undecidable-word-problem]]), in which a
`Pi^0_2` event (every stage eventually confirmed) keeps the group amenable
while its failure makes a free subgroup appear.  The two-generator
recursive family [[shift-raag-family-classifies-amenability]] shows the
shape of the switch; its finite-presentation analogue would need the
relators `[a, t^j a t^-j]` for all `j` to be consequences of finitely many,
which is exactly what fails.
