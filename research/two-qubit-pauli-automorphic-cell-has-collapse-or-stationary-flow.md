---
rg: 2
id: two-qubit-pauli-automorphic-cell-has-collapse-or-stationary-flow
kind: claim
title: A finite automorphic mixed cell over the Pauli packet either collapses the forbidden atom or has an exact stationary countermodel
distinct_from:
  two-qubit-pauli-frame-covers-common-d8-source: that constructs the minimal frame and computes one universal collapsing word; this classifies every phase-safe automorphic continuation of that packet by a stationary finite model.
  central-character-regular-flow-defeats-finite-d8-return: that constructs a character-sector representation for finite graphs of packet groups; this adds the forbidden projection and finite-word canonical-trace tests needed by the CPS12 leakage inequality.
  residually-finite-models-refute-filtered-wandering-return: that treats one filtered wandering moment in an arbitrary residually finite group; this gives the Pauli-frame collapse-or-flow dichotomy and tests both the induced and orthogonal-amalgam models.
  algebraic-selector-mixing-frame-collapses-forbidden-sector: that proves universal collapse from an abstract exact frame; this identifies the complementary automorphic class and the minimum non-automorphic escape.
---

Let `K` be the central product of the two D8 packets in `(TPF1)`, let
`P=(1-y)/2`, and let `0!=F<=P` be a forbidden selector projection in
`C[K]`.  There are two finite-packet continuations relevant to the proposed
mixed-cell return.

The first makes the Pauli frame and its selector-mixing rows universal
group-algebra identities.  The second is a **phase-safe automorphic
continuation**, assembled using only:

1. finite packet multiplication tables and finite Weyl/Clifford tables;
2. stable letters conjugating one finite packet subgroup isomorphically
   onto another; and
3. a finite graph of such finite vertex and edge groups, with every edge
   embedding injective and preserving the common central involution `y`.

These two continuations have opposite exact outcomes.

* If the packet identities and the mixed rows supply the exact Pauli frame
  and exact selector-mixing equations used in `(NSF4)--(NSF5)`, they imply

  ```text
  F=0 in C*(Gamma).                                    (PAC1)
  ```

  Thus the map `C[K]->C*(Gamma)` is not injective.  In particular the
  induced representation containing the rejected packet type cannot be a
  representation of this quotient.

* For every phase-safe automorphic continuation in which the literal copy of
  `K` embeds in the resulting fundamental group `Gamma`, the cells admit an
  exact finite-dimensional model
  in which

  ```text
  tr(F)>0                                               (PAC2)
  ```

  and every defining relator has zero defect.  Moreover, for every finite
  word window one may choose such a model to have canonical trace on that
  window and

  ```text
  tr(F)=tau_K(F).                                      (PAC3)
  ```

  Hence no dimension-independent inequality of the CPS12 form

  ```text
  c tr(F) <= sum_(mixed cells r) ||r-1||_2^2
               + filtered canonical-trace errors,     c>0,              (PAC4)
  ```

  follows from automorphic packet syntax.

The second branch includes the orthogonal-amalgam countermodel: restriction
multiplicities are a stationary flow, while tree and chord intertwiners may
be chosen independently inside the matching isotypic multiplicity spaces.
Thus a transverse Pauli/Clifford conjugacy rotates the uncovered forbidden
mass but cannot consume it.

This theorem is deliberately restricted to the universal-frame and
automorphic alternatives above.  An arbitrary extra group relator need not
define a graph of finite groups, so the theorem does not assert that every
finite-word two-cell is residually finite.  It does show exactly what the
next cell must add.  It must be a
non-automorphic proper-corner or unequal-index return whose infinite
commuting witness is absorbed by countable amplification, while its rank
loss is detected only in finite matrices.  The localization or containment
step must itself be matrix-only: if it is a universal group-algebra identity,
the regular-factor trace collapses the exit just as in `(UBR4)`.  Equivalent
minimum escapes are an integer-multiplicity/capacity gate or a genuinely
self-similar unequal-index recurrence.  More finite packet tables, Clifford
normalizers, or Bass--Serre incidence cannot close `(CPS12)`.
