---
rg: 2
id: finite-adaptive-selected-atom-ring-tree
kind: claim
title: Conditional partial isometries realize the entire bounded selected-atom tree in one finite coefficient ring
distinct_from:
  finite-depth-adaptive-selected-atom-escape-tree: That asks for ordinary-group words in every normalized-HS microstate; this is the exact finite coefficient-ring construction before metric group decoding.
  shared-bcs-carrier-localizes-free-compressor-quotient: That localizes a free self-compressor quotient on one forbidden carrier; this directly installs the finitely many adaptive escape arrows and needs no infinite compressor.
  schur-idempotent-is-an-injective-toeplitz-defect: That realizes one predicate idempotent as a Toeplitz defect; this realizes a bounded branching tree of predicate-selected partial isometries.
---

**ESTABLISHED ALGEBRAIC COMPILER.**  Fix a depth `N`.  Work over a fixed
characteristic-zero splitting ring containing `1/2`.  Start with the shared
BCS involutions, the one-bit selector packet, and the Pauli seed.  For every
node `sigma in {1,...,M}^{<N}` name a projection `q_sigma`; put

```text
q_empty=q_-(1+B)/2.
```

For every node and forbidden type `i`, put

```text
a_(sigma,i)=q_sigma P_i R_i,
```

and impose the finite commutation relations which make this a projection.
Adjoin two formal adjoint coefficient letters `s_(sigma,i),sbar_(sigma,i)`
and a projection `d_(sigma,i)` with

```text
sbar_(sigma,i)s_(sigma,i)=a_(sigma,i),
s_(sigma,i)sbar_(sigma,i)=d_(sigma,i),
s_(sigma,i)a_(sigma,i)=s_(sigma,i),
d_(sigma,i)s_(sigma,i)=s_(sigma,i),
a_(sigma,i)sbar_(sigma,i)=sbar_(sigma,i),
sbar_(sigma,i)d_(sigma,i)=sbar_(sigma,i),
d_(sigma,i)q_sigma=q_sigma d_(sigma,i)=0,               (FAR1)
q_(sigma i)=q_sigma+d_(sigma,i).                        (FAR2)
```

Finally impose that every `q_(sigma i)` commute with the shared BCS and
selector letters needed to form the next family of assignment projections.
There are only

```text
1+M+...+M^N
```

nodes, so this is one finite ring presentation.

In every finite-dimensional star representation, normalized rank/trace is
invariant under the two products in `(FAR1)`.  Therefore

```text
tr(q_(sigma i))=tr(q_sigma)+tr(a_(sigma,i)).             (FAR3)
```

For the maximal type, `(MFA2)` turns `(FAR3)` into the exact supercritical
tree recurrence.  Thus the coefficient presentation already contains all
the desired payload-conditioned placement; no address register or
simultaneous routing of the `M` types is needed.

The presentation has the required exact finite-tracial consistency model.
In the perfect BCS model every forbidden `P_i` is zero.  Set every
`s_(sigma,i),sbar_(sigma,i),d_(sigma,i)` to zero and every `q_sigma` to
`q_empty`.  Then `(FAR1)--(FAR2)` hold, the Pauli seed remains nonzero, and
`J=-1` survives.  Hence the trace growth is finite-matrix-only and is not a
universal finite-tracial inequality.

All equations are finite polynomial ring equations.  Rank-five Steinberg
wordization and `atlas-steinberg-context-absorption` can encode their
generated two-sided ideal with finitely many ordinary group relators.  What
that wordization does not provide is a metric coefficient interpretation of
an arbitrary normalized-HS microstate.

The equal-source/range part is nevertheless group-visible.  By
`murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness`, the explicit
two-by-two involution built from each arrow conjugates the stabilized source
idempotent to its stabilized range.  Hence every unitary representation of
the wordized group gives the two associated root words identical spectral
data.  The remaining decoder is not equality of their sizes; it is placing
the orthogonal sum `q_sigma+d_(sigma,i)` on the same physical carrier as the
decoded BCS corner.
