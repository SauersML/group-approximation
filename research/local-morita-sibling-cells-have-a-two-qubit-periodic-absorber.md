---
rg: 2
id: local-morita-sibling-cells-have-a-two-qubit-periodic-absorber
kind: claim
title: Local Morita sibling cells have a depth-independent two-qubit periodic absorber
artifacts:
  - research/local-morita-sibling-periodic-absorber-proof.md
distinct_from:
  orthogonal-heisenberg-self-copy-skeleton-has-marked-microstates: that builds growing Schrödinger models for every finite window of the full infinite Heisenberg self-copy skeleton; this gives one fixed four-dimensional model for every depth when only local sibling Pauli cells are retained.
  dyadic-affine-pauli-patterns-have-odd-periodizations: that periodizes arbitrary finite affine address patterns on a growing odd orbit; this identifies the smaller two-state reuse already available in the binary Morita tree before any address geometry is imposed.
  stabilized-morita-branches-are-inner-but-incoherent: that constructs the actual stabilized branch words and identifies unbounded global-frame coherence; this proves the finite Pauli normal form showing why nodewise use of those words cannot supply that coherence.
---

**ESTABLISHED.**  Let `X,Z` be the two Pauli
involutions on `C^2`, and work on

```text
K=C^2 tensor C^2.
```

Inside `U(K)` put

```text
P_0=<X tensor I, Z tensor I, J>,
P_1=<I tensor X, I tensor Z, J>,       J=-I_K,          (LMS1)
```

and let `S` be tensor swap.  The two marked Pauli groups commute elementwise,
intersect in `<J>`, and satisfy

```text
S P_0 S^(-1)=P_1,       S P_1 S^(-1)=P_0.              (LMS2)
```

For every binary word `u`, let `epsilon(u)` be its parity and set

```text
P_u=P_(epsilon(u)).                                      (LMS3)
```

Then at every vertex, at every depth,

```text
P_(u0)=P_u,              P_(u1)=S P_u S^(-1),           (LMS4)
```

and the two sibling groups `P_(u0),P_(u1)` commute modulo their common
central involution `J`.  Each child is unitarily conjugate to its parent,
every same-site Pauli relation is exact, every sibling cross commutator is
exactly one, and the marked sector `J=-1` is all of `K`.  Nevertheless only
the two groups in `(LMS1)` ever occur, so the representation dimension stays
equal to four independently of the tree depth.

Equivalently, the local binary recursion

```text
parent packet -> two conjugate commuting marked children                 (LMS5)
```

does not imply that packets at distinct leaves are independent.  Cousins
may reuse the same Pauli factor periodically.  Iterating a fixed inner branch
word and checking one sibling cell at every addressed vertex therefore does
not instantiate the growing-capacity hypothesis of
`opnorm-coordinatewise-capacity-diagonal`.

This separates two statements which are identical in the intended Leavitt
module but not in arbitrary unitary tuples.  The actual coefficient identity

```text
H(R)=alpha_0(H(R)) alpha_1(H(R))                        (LMS6)
```

uses the range-sum relation to express every parent coefficient through
specific preimages in both children.  A finite Pauli sibling cell records
only conjugacy, commutation, and the common phase; it does not record
`(LMS6)`.  In particular it cannot recover the atomic completeness row

```text
s_0t_0+s_1t_1=p_U.                                     (LMS7)
```

Consequently the moving-window attack on
`binary-leavitt-three-row-atomic-compiler` must authenticate a genuinely
coefficient-sensitive parent-generation occurrence, or an equivalent row
which detects reuse of one Pauli factor in two different cousin branches.
Local branch conjugacy, same-site Pauli relations, and sibling commutation
can be used as supporting rows, but no iteration of them alone yields the
unbounded finite-coordinate challenge.
