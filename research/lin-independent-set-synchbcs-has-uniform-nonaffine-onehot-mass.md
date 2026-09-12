---
rg: 2
id: lin-independent-set-synchbcs-has-uniform-nonaffine-onehot-mass
kind: claim
title: Every perfect trace of the Lin independent-set SynchBCS has uniformly positive nonaffine one-hot mass
artifacts:
  - research/lin-independent-set-nonaffine-onehot-support-proof.md
distinct_from:
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: that gives an existential BCS/LCS equivalence; this proves that the canonical Lin--independent-set SynchBCS lies on the negative side of its local-support hypothesis for every perfect trace.
  binary-tracial-two-csp-has-classical-solution: that collapses a Boolean unary-binary tracial CSP; this uses it after support-restricting every one-hot question to at most two outcomes.
  perfect-qc-separation-yields-finite-bcs-with-no-matrix-model: that constructs the source; this audits its actual one-hot supports and the precise local toric/LCS obstruction.
---

Let `I` be the finite independent-set game obtained from Lin's fixed
synchronous separation, so

```text
omega_co(I)=1,                  omega_*(I)<1.             (LNO1)
```

Write `e_(i,v)` for the canonical projection PVM of independent-set
question `i`, and let `T(A_I)` be the nonempty compact space of traces on
its synchronous algebra.  For `tau in T(A_I)`, put

```text
w_(i,v)=tau(e_(i,v)),
r_i(tau)=1-(sum of the two largest w_(i,v)),
eta(tau)=max_i r_i(tau).                                 (LNO2)
```

Then there is a source-dependent constant `eta_0>0` such that

```text
eta(tau)>=eta_0                 for every tau in T(A_I). (LNO3)
```

In particular every perfect trace has a question `i` with at least three
positive outcome projections.  In the canonical SynchBCS presentation those
outcomes are one-hot atoms.  If `u,v,w` are three positive outcomes, their
odd affine sum

```text
e_u+e_v+e_w in F_2^(V(I))                              (LNO4)
```

is a three-hot forbidden assignment.  Hence the affine hull of the positive
local support is not contained in the one-hot predicate.  The
locally-affine-support criterion fails for **every** trace of this canonical
source; choosing an extreme, support-minimal, or otherwise special perfect
trace cannot make its direct affine-support relaxation into an LCS.

There is a corresponding local gadget no-go.  The projection of the scalar
solution set of any finite binary parity gadget (including affine auxiliary
bits) is affine.  If every positive one-hot atom has a scalar auxiliary
extension, that projection contains their affine hull and therefore contains
the forbidden three-hot point in `(LNO4)`.  Thus the canonical source is
not context-locally torically determined and cannot be encoded by an
atomwise scalar-extendable binary LCS gadget.

This does not rule out a global compiler with shared noncommuting auxiliaries.
It identifies what such a compiler must do: its ancillary sector must be
nonreducing across the positive atoms, must couple different contexts, and
must defeat the odd-product extension.  A finite sheet-transport atlas is
insufficient by `finite-sheet-transport-networks-are-exactly-matricial`.

The quantitative endpoint is clean.  If a global finite LCS compiler has a
perfect-state decoder back to `I`, then it has no Connes-embeddable perfect
state, so compactness of the finite `qa` correlation set gives a strict
`qa<1` gap.  If the decoder moreover satisfies

```text
Loss_I(Decode(S)) <= C Loss_L(S)                         (LNO5)
```

for finite-dimensional strategies, then

```text
1-omega_qa(L) >= (1-omega_*(I))/C.                      (LNO6)
```

Exact algebraic satisfiability preservation without either a perfect-state
decoder or a bound such as `(LNO5)` does not preserve the needed
quantum-approximable gap.
