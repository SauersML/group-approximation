---
rg: 2
id: hyperbolic-rf-question-equals-vtf-question
kind: claim
title: Some hyperbolic group fails residual finiteness exactly when some hyperbolic group fails virtual torsion-freeness
distinct_from:
  finite-torsion-carrier-virtual-torsionfree-criterion: that is a criterion inside one group; this compares existence across groups, and passing from a torsion-free residual to one containing torsion needs a Dehn filling that changes the group
  rips-kernel-target-iff-hyperbolic-nonrf: that equates the Rips-kernel target with the residual-finiteness question; this equates Lück's virtual torsion-freeness question with it
  hyperbolic-prime-torsion-residual-dichotomy: that classifies where prime torsion in a finite residual can sit; this proves such torsion exists in some hyperbolic group as soon as any hyperbolic group fails residual finiteness
---

The following existential assertions are equivalent.

1. Some word-hyperbolic group is not residually finite.
2. Some word-hyperbolic group is not virtually torsion-free.

Equivalently, every word-hyperbolic group is residually finite **if and only
if** every word-hyperbolic group is virtually torsion-free.  For a single group
the two properties differ (virtual torsion-freeness only asks finite quotients
to see torsion), but as universal questions they are one question: the roots
`non-residually-finite-hyperbolic-group` and
`hyperbolic-groups-virtually-torsion-free` (Lück 2008, Problem 11.1(i)) are
answered together.

**Sharp form of (1) => (2).**  Let `G` be word-hyperbolic with
`R_f(G) != 1`.  Either `R_f(G)` already contains a nonidentity element of
finite order, so `G` itself is not virtually torsion-free; or `R_f(G)` is
torsion-free, and then for every `1 != g in R_f(G)` there is `k >= 1` such that
for all sufficiently large `j` the filling

```text
Q_j = G / <<g^(kj)>>
```

is word-hyperbolic, the image of `g` in `Q_j` is a nonidentity element of
finite order dividing `kj`, and that image lies in `R_f(Q_j)`.  So `Q_j` is not
virtually torsion-free.

The proof is complete in `hyperbolic-rf-question-equals-vtf-question-proof`,
modulo two imported theorems of Osin
(`relatively-hyperbolic-dehn-filling`,
`hyperbolic-group-relative-to-maximal-elementary-subgroup`), both read
verbatim from the arXiv PDFs on 2026-09-11.  No historical novelty is claimed:
secondary sources state this equivalence without proof, and the argument here
is supplied so the graph does not rest on that statement.  Not Lean-verified.

**Consequence for attacks.**  Any construction aimed at either root is an
attack on both, and any obstruction to one is an obstruction to the other.  In
particular, the four live routes into `non-residually-finite-hyperbolic-group`
are routes into `non-virtually-torsion-free-hyperbolic-group` through
`non-vtf-hyperbolic-via-residual-cyclic-filling`.
