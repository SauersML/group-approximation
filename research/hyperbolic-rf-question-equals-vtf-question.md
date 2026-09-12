---
rg: 2
id: hyperbolic-rf-question-equals-vtf-question
kind: claim
title: Some hyperbolic group fails residual finiteness exactly when some hyperbolic group fails virtual torsion-freeness
distinct_from:
  finite-torsion-carrier-virtual-torsionfree-criterion: that is a criterion inside one group; this compares existence across groups, and passing from a torsion-free residual to one containing torsion needs a Dehn filling that changes the group
  rips-kernel-target-iff-hyperbolic-nonrf: that equates the Rips-kernel target with the residual-finiteness question; this equates Lück's virtual torsion-freeness question with it
  hyperbolic-prime-torsion-residual-dichotomy: that classifies where prime torsion in a finite residual can sit; this proves such torsion exists in some hyperbolic group as soon as any hyperbolic group fails residual finiteness
artifacts:
  - research/artifacts/hyperbolic-rf-vtf-osin-full-proof-2026-09-11.md
---

The following existential assertions are equivalent.

1. Some word-hyperbolic group is not residually finite.
2. Some word-hyperbolic group is not virtually torsion-free.

Equivalently, every word-hyperbolic group is residually finite **if and only
if** every word-hyperbolic group is virtually torsion-free.  For a fixed
hyperbolic group, virtual torsion-freeness only asks finite quotients to see
torsion; this argument asserts no converse inside that same group.  As
universal questions they are one question: the roots
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

is word-hyperbolic, the image of `g` in `Q_j` has order exactly `kj > 1`,
and that image lies in `R_f(Q_j)`.  So `Q_j` is not
virtually torsion-free.

The proof is complete in `hyperbolic-rf-question-equals-vtf-question-proof`,
modulo two imported theorems of Osin
(`relatively-hyperbolic-dehn-filling`,
`hyperbolic-group-relative-to-maximal-elementary-subgroup`), both read
from the arXiv PDFs on 2026-09-11), together with the standard finite
torsion-carrier theorem for hyperbolic groups.  The finite-quotient arguments,
normal cyclic filling construction, and exact torsion order are proved in the
route and linked artifact.  No historical novelty is claimed: Daniel T. Wise,
*Complete square complexes*, Comment. Math. Helv. **82** (2007), 683--724,
Proposition 9.2 and Theorem 9.3, already give the equivalence via a
power-quotient argument; `universal-hyperbolic-vtf-iff-rf` records that primary
source.  This equivalence does not establish either counterexample.
Not Lean-verified.

**Consequence for attacks.**  Any construction aimed at either root is an
attack on both, and any obstruction to one is an obstruction to the other.  In
particular, the four live routes into `non-residually-finite-hyperbolic-group`
are routes into `non-virtually-torsion-free-hyperbolic-group` through
`non-vtf-hyperbolic-via-residual-cyclic-filling`.

## Prior-art check (lit-groups, 2026-09-11)

Requested by the coordinator. Sources read, all from their arXiv PDFs
(text extracted on MSI):

- **Kapovich–Wise**, J. Algebra 223 (2000), in the verbatim quotation of
  Niblo–Williams, arXiv:math/0209185v1, p. 744. The quoted theorem lists only
  "(i) Every word-hyperbolic group is residually finite. (ii) Every
  word-hyperbolic group has at least one proper finite index subgroup." That is
  `kapovich-wise-rf-iff-finite-quotients`; virtual torsion-freeness does not
  appear in it.
- **Lück**, arXiv:0806.3771v2, §11.1, lists "(i) Is every hyperbolic group
  virtually torsionfree?" and "(ii) Is every hyperbolic group residually
  finite?" as separate questions, with no equivalence stated.
- **Minasyan**, arXiv:math/0506606v2, and **Sisto–Wilton**, arXiv:2410.00556v2:
  engulfing and residual-finiteness statements only. Neither states this
  equivalence.

No prior statement of the residual-finiteness / virtual-torsion-freeness
equivalence was found in these sources. The primary Kapovich–Wise paper was not
accessible (publisher paywall, no arXiv copy found), so a statement there beyond
the quoted theorem is not excluded. The Dehn-filling proof here stands as this
graph's route.
