---
rg: 2
id: binary-leavitt-unit-group-has-tt-mod-t
kind: claim
title: The binary Leavitt unit group has property (TT) modulo T, and so does every elementary group over the algebra
distinct_from:
  property-tt-mod-t-rigidity-for-elementary-groups: That is the general theorem, whose conclusion is conditional on four ring hypotheses -- finite type, a binary Leavitt family, single-sandwich division and a trivial elementary diagonal class -- and names no group; this discharges all four for one algebra and names the group, so it is the hypothesis-free specialization rather than a restatement.
  leavitt-gl-equals-el-and-perfect-unit-group: That is pure algebra over the same ring -- GL equals EL at every rank, and the unit group is perfect -- with no representation, cocycle or approximation property in it; this is an analytic rigidity statement about quasi-cocycles, and it consumes that algebra as the identification carrying rank two to the unit group.
  openai-leavitt-unit-nonsofic: That is the soficity status of this very group; this asserts a rigidity property and is deliberately proved outside the nonsoficity theorem's dependency closure, so that a reader checking (TT)/T need not trust the compression criterion. Their conjunction is a corollary recorded below.
  binary-leavitt-unit-group-hyperlinear: That asks whether the same group has normalized Hilbert--Schmidt models, and is OPEN; this is established, is about Hilbert-space quasi-cocycles rather than approximate models, and decides nothing about that fork.
artifacts:
  - GroupApproximation/PropertyTT/PaperStatements.lean
  - GroupApproximation/PropertyTT/NonsoficCorollary.lean
  - GroupApproximation/PropertyTT/FiniteTypeLeavittTT.lean
  - docs/PROPERTY_TT_CLAIM_MAP.md
  - property_tt_leavitt.tex
---

ESTABLISHED, machine-checked, with no hypothesis left standing.  Write
`L = L_(F_2)(1,2)`.  `PropertyTT/PaperStatements`:

* `binaryLeavitt_elementaryGroup_hasTTmodT n (hn : 2 <= n)` -- `EL_n(L)` has
  property `(TT)/T`: every Hilbert-space quasi-cocycle into a unitary
  representation with no nonzero invariant vector is bounded;
* `binaryLeavitt_elementaryEquivUnits n (hn : 2 <= n)` -- the left-comb
  prefix code identifies `EL_n(L)` with `L^x` itself;
* `binaryLeavittUnits_hasTTmodT` -- hence `L^x` has `(TT)/T`.

The three structural hypotheses of the general theorem are theorems here, not
assumptions: the canonical generators are a binary Leavitt family by
definition, single-sandwich division is
`Leavitt/LeavittSimplicity.exists_mul_mul_eq_one`, and the elementary diagonal
class is `KOne` (`diagUnit_mem_elementary`,
`BinaryLeavitt.elementaryGroup_eq_top`).  Finite type is the presentation.

## Rank two is not a low-rank analogue

The quantitative root estimate behind the general theorem is proved in **rank
four**, over a free characteristic-two algebra; rank two is reached afterwards,
because the binary Leavitt self-similarity `M_n(L) ~= L` makes `EL_2(L)` and
`EL_4(L)` the same group.  So this is not a rank-two version of a
universal-lattice argument -- no rank-two estimate is ever proved -- and that
is the only reason a rank-two elementary group can carry `(TT)/T` at all.

## The conjunction, and why it is kept downstream

`PropertyTT/NonsoficCorollary.binaryLeavitt_elementaryGroup_hasTTmodT_and_not_isSofic`
records that for every `n >= 2` the group `EL_n(L)` has `(TT)/T` **and** is not
sofic, by combining the above with
[[openai-leavitt-unit-nonsofic]] through the same unit-group equivalence.  That
module sits deliberately outside the dependency closure of the rigidity
theorems, and the conjunction is only a corollary: nothing in the `(TT)/T`
proof uses nonsoficity, and nothing here re-proves it.

## Credit boundary

The `(TT)/T` conclusion is the only part this development claims.  Property
`(TT)/T` and the relative-to-global mechanism are Mimura's
(arXiv:1106.3769).  The algebraic identifications `GL_n(L) = EL_n(L)` and
`GL_n(L) ~= L^x` are Khanh--Thanh's (*Matrix generators for the unit groups of
L_K(1,d)*, arXiv:2607.10351, Lemma 4.1, Proposition 4.2, Corollary 4.4), resting on
`K_1(L_k(1,2)) = 0` from Ara--Brustenga--Cortinas and the GE theorem of
Menal--Moncasi as applied by Ara--Goodearl--Pardo; the formal companion reaches
the same equalities by a constructive pencil reduction instead, so no
`K`-theory is an axiom here.  The nonsoficity in the corollary is OpenAI's, by
the mechanism of Kun and Kun--Thom.  Neither this node nor the manuscript may be
read as an independent proof of any of those.

## What it does and does not buy the program

`(TT)/T` is strictly stronger than property `(T)`, which this group was already
known to have, and it bounds quasi-cocycles rather than cocycles -- the point
being that the bounded error in the cocycle identity accumulates along a long
word, so finite generation alone gives no global bound.  It says nothing about
normalized Hilbert--Schmidt models, so it leaves
[[binary-leavitt-unit-group-hyperlinear]] exactly where it was.
