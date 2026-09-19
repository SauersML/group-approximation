---
rg: 2
id: exel-loring-relative-quasirep-invariant
kind: claim
title: Exel--Loring two-homology invariants of quasi-representations survive where K-one dies
distinct_from:
  matrix-corona-k1-vanishes: that is the negative fact that a single marked unitary carries no corona K_1 class; this is the positive external construction of the relative invariant that survives, built from a pair rather than one element
  effective-transport-modulus: that asks for a numerical modulus for the operator-norm obstruction; this records a homological invariant of quasi-representations, not a modulus
---

`matrix-corona-k1-vanishes` establishes that no invariant of the marked
unitary *alone* can obstruct a corona representation, and closes with the
observation that "any surviving index argument must be relative — an
invariant of the mark **together with** another almost-commuting operator,
as in the Bott index of an almost commuting pair".  The literature already
contains the developed form of exactly that invariant.

**Dadarlat, *Quasi-representations of groups and two-homology*,
arXiv:2111.05755** (2021-11-18).  Verified from the abstract: the paper
generalizes the **Exel--Loring formula** for quasi-representations of
countable discrete groups, and shows nontriviality of the resulting
invariants "for quasidiagonal groups which are coarsely embeddable in a
Hilbert space and have nonvanishing second Betti number".

The Exel--Loring formula is the group-level form of the Bott index of an
almost commuting pair: it pairs a quasi-representation against a class in
`H_2` of the group, and the invariant lives where a single unitary's `K_1`
class does not.  So the relative index programme that
`matrix-corona-k1-vanishes` calls for is not hypothetical — it has an
existing home, and the natural first question for this repository is what
that invariant does on the marked pair of the literal construction.

Companion, same author: **Dadarlat, *Obstructions to matricial stability of
discrete groups and almost flat K-theory*, arXiv:2007.12655** — matricial
stability implies vanishing of rational cohomology in nonzero even
dimensions.  (This is already cited in the repository for its Lemma 3.18 and
Proposition 3.19; the *stability obstruction* half of the paper is the part
relevant here.)

**Caveat, now discharged for the first paper.**  The primary text of
arXiv:2111.05755v1 has been read: Theorem 1.1, its tracial form equation
(3), and Theorem 3.2.  The pairing, the norm (operator), and the
dimension-independent finite set and defect bound are recorded in
`exel-loring-mark-quantization`, along with the two hypotheses that block
the intended deployment.  One correction belongs here.  The second Betti
number hypothesis sits in Theorem 3.2, whose standing hypothesis is that the
group is **quasidiagonal** — and a quasidiagonal group is MF.  So that
nontriviality criterion cannot be applied to a non-MF candidate at all, and
checking Betti numbers against a candidate is not the live question; what
transfers is Theorem 1.1, which assumes nothing beyond countability.
arXiv:2007.12655 remains abstract-level only.
