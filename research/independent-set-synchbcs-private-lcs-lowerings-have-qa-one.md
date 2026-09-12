---
rg: 2
id: independent-set-synchbcs-private-lcs-lowerings-have-qa-one
kind: claim
title: Every private local LCS lowering of the perfect independent-set SynchBCS has qa value one
artifacts:
  - research/independent-set-affine-hull-and-private-magic-square-proof.md
distinct_from:
  lcs-parity-gadgets-preserve-odd-dictator-affine-hull: that is the generic atomwise affine-closure theorem; this computes the two predicates in the canonical 2025 independent-set BCS, glues their local ghosts globally, and obtains a one-dimensional negative-J model.
  magic-square-one-port-is-a-universal-phase-absorber: that classifies one local contextual cell; this applies all audited private and common-row cells to one global source assignment and concludes that the compiled game has qa value one.
  perfect-qc-separation-yields-finite-bcs-with-no-matrix-model: that supplies the no-matrix SynchBCS source; this proves that the most direct LCS and Magic-Square lowerings destroy its strict qa gap.
  perfect-completeness-constant-soundness-lcs-compiler: that is the open unrestricted compiler; this closes only source-oblivious context-local and the explicitly listed Magic-Square architectures.
---

**ESTABLISHED SOURCE-SPECIFIC NO-GO; THE SHARED CYCLIC COMPILER
REMAINS OPEN.**

Let \(I\) be the finite independent-set game and \(B_I\) its canonical
SynchBCS from
perfect-qc-separation-yields-finite-bcs-with-no-matrix-model.
Write \(\xi_{i,v}\in\mathbf F_2\) for the bit selecting outcome \(v\) on
question \(i\). The only scalar predicate supports in this presentation
are

\[
 E_m=\{e_1,\ldots,e_m\}
 \quad\hbox{and}\quad
 N=\{(0,0),(1,0),(0,1)\},                               \tag{ISL1}
\]

where \(E_m\) is exact-one and \(N\) is the forbidden-overlap, or NAND,
support. Equivalently, the canonical presentation may split exact-one into
one odd-parity equation and the within-question copies of \(N\).

Consider a context-local binary LCS lowering with the following exact
hypotheses.

1. Every source bit is a shared visible scalar port.
2. Each source predicate \(C\) is replaced by finitely many parity
   equations on its visible ports and a finite auxiliary set \(A_C\).
3. The sets \(A_C\) are disjoint for distinct source predicates.
4. In the sector \(J=-1\), every scalar assignment in the support of \(C\)
   has a scalar satisfying extension to \(A_C\).

Then the output LCS has a one-dimensional representation with \(J=-1\).
Consequently its associated game has

\[
 \omega^{\mathrm{cl}}=\omega^q=\omega^{qa}
 =\omega^{\mathrm{co}}=1.                              \tag{ISL2}
\]

The proof is the source-specific affine-hull computation

\[
 \operatorname{Aff}(E_m)
   =\left\{x\in\mathbf F_2^m:\sum_jx_j=1\right\},
 \qquad
 \operatorname{Aff}(N)=\mathbf F_2^2.                  \tag{ISL3}
\]

Choose one arbitrary outcome \(v_i\) for every question. The resulting
visible vector lies in \(E_m\) on every exact-one context. On every
forbidden-pair context it may equal \((1,1)\), but (ISL3) and projection of
affine solution sets show that \((1,1)\) also extends through its local LCS
gadget. Private auxiliaries then glue all these extensions. Thus every
graph edge has disappeared before any operator analysis begins.

The same conclusion holds for the following attempted contextual repairs.
One may replace or augment the private predicate gadgets by any finite
collection assembled from:

- disjoint one-port Magic Squares;
- families of Magic Squares glued along one common full row, with arbitrary
  and even mutually noncommuting source ports;
- private transverse two-port Magic Squares; and
- disjoint finite tensor products of the preceding blocks.

A one-port square realizes both port signs. A common-row family realizes
every tuple of source involutions in one four-dimensional amplification.
A transverse two-port square realizes exactly the commuting pairs. Hence
every scalar port profile from the global assignment above extends through
every listed block, and the finitely many private blocks can be placed on
separate tensor factors. The resulting target again has an exact
finite-dimensional perfect strategy, so its qa value is one.

This does not rule out a lowering tailored to the smaller support of one
chosen non-Connes-embeddable trace. It also does not cover source-dependent
ancillas shared around a genuine cycle, higher-occurrence cross-context
relations, or a compiler that begins with a marked group element already
proved to lie in the approximate radical. Those are exactly the surviving
interfaces.

Finally, merely arranging that the solution-group sign has no exact
finite-dimensional negative sector would still not prove
\(\omega^{qa}<1\). The repository's regular shared-center spin model has a
nontrivial central involution killed by every exact finite-dimensional
representation while finite spin quotients keep it macroscopically
separated with zero fixed-window defect. Thus a successful LCS compiler
must preserve the source's qa gap by a dimension-independent approximate
decoder. Ordinary exact Slofstra-style group embedding is not a substitute.

No nonhyperlinear group is claimed here.

DERIVATION
independent-set-affine-hull-and-private-magic-square-proof
