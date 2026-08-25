---
rg: 2
id: three-face-quotient-separators-are-not-one-face-local
kind: claim
title: Three-face quotient separators have a quantitatively essential tree-face component
distinct_from:
  exhausting-ideal-reservoirs-have-lift-or-quotient-separator: that produces an abstract quotient-level separator when exhausting reservoir distance stays positive; this analyzes such a separator on the concrete three-face system and proves that symmetry averaging cannot concentrate it on one face.
  explicit-finite-face-ucp-section-is-edge-equivariant: that constructs a ucp section on the closing finite face; this uses that section, after the subgroup Fourier expectation, to rule out every closing-face-supported separator.
  three-face-ucp-balancing-needs-macroscopic-tree-motion: that gives a positive Gram obstruction to canonical tree-face values; this shows only that the same closing-face Gram cycle cannot by itself be a quotient nonliftability separator.
  equal-difference-gram-averaging-fails-at-four-free-words: that shows truncated equal-difference averaging need not preserve positivity; this averages a linear separator only over genuine compatible automorphisms, for which the ucp comparison class is invariant.
---

**ESTABLISHED (quantitative finite-dimensional normal form).**  In the explicit `(3,3,4)`
Kac--Moody triangle put

```text
A=C^*(G_0),       Q=C^*(Lambda),
S_Delta=C^*(P_12)+C^*(P_23)+C^*(P_13) subset Q,
q:A->>Q.                                                    (SQS1)
```

Each `P_ij` is finite, so `S_Delta` is finite-dimensional.  Suppose a bounded
real functional `ell` on `L_sa(S_Delta,Q)` is a quotient separator of the
type supplied by `(ERD3)`:

```text
ell(id_(S_Delta)-q phi)>=delta>0
                    for every phi in UCP(S_Delta,A).       (SQS2)
```

Let `Omega` be any finite group of **compatible triangle symmetries**: for
each `omega` there are star automorphisms

```text
alpha_omega of A,       beta_omega of Q,
q alpha_omega=beta_omega q,       beta_omega(S_Delta)=S_Delta. (SQS3)
```

Then the Reynolds average of `ell` over `Omega` is `Omega`-invariant and
still satisfies `(SQS2)` with the same `delta`.

For each face `H in {P_12,P_23,P_13}`, let

```text
M_H(u_g)=1_H(g)u_g,             g in Lambda,               (SQS4)
```

be the subgroup Fourier expectation, restricted to `S_Delta`.  It is ucp
and is the identity on `C^*(H)`.  Moreover it is liftable through `q`:

- for `H=P_12,P_23`, compose `M_H` with the canonical face embedding into
  `A`;
- for `H=P_13`, compose `M_H` with either explicit finite-face ucp section
  from `explicit-finite-face-ucp-section-is-edge-equivariant`.

Consequently every separator satisfying `(SQS2)`, symmetrized or not, obeys

```text
ell(id-M_H)>=delta,       H=P_12,P_23,P_13.                (SQS5)
```

Call a functional `H`-local if it factors through restriction of a map to
`C^*(H)`.  Equation `(SQS5)` immediately implies

```text
boxed: no quotient separator is H-local for any one face H. (SQS6)
```

Indeed `(id-M_H)|_(C^*(H))=0`, so every `H`-local functional vanishes on
`id-M_H`, contradicting `(SQS5)`.

In particular the prefix Gram/cyclic-holonomy witness attached to

```text
n=a_1...a_L in ker(P_1*_(P_0)P_3->>P_13)
```

is `P_13`-local: every entry of its matrix

```text
G_n=[u_(g_i^(-1)g_j)]_(0<=i,j<=L)
```

belongs to `C^*(P_13)`.  Hence no averaging of `(SQS2)` through compatible
triangle symmetries can reduce the separator to this finite cyclic-holonomy
functional.  The explicit one-face section does not contradict a genuine
separator; it proves that a genuine separator must retain information
transverse to that face.

There is also a bounded quantitative face normal form.  Because `S_Delta` is
finite-dimensional and is the sum of its three face algebras, choose bounded
real self-adjoint linear maps

```text
R_ij:S_Delta->C^*(P_ij),       R_12+R_23+R_13=id.          (SQS7)
```

For example, choose a real self-adjoint basis of `S_Delta` from the union of
bases of the three face algebras, assign each basis vector to one face, and
let `R_ij` be the corresponding coordinate projection.  For
`psi:C^*(P_ij)->Q`, put

```text
ell_ij(psi)=ell(psi o R_ij).                               (SQS8)
```

Then each `ell_ij` is bounded and

```text
ell(psi)=sum_(ij) ell_ij(psi|_(C^*(P_ij))).                (SQS9)
```

This is a genuine bounded splitting: composition with each fixed `R_ij` is
bounded on the map space, and `(SQS9)` follows from `sum R_ij=id`.

Set `D_13=id-M_(P_13)`.  Since `D_13` vanishes on `C^*(P_13)`, `(SQS5)` and
`(SQS9)` give

```text
ell_12(D_13|_(C^*(P_12)))
 +ell_23(D_13|_(C^*(P_23))) >= delta.                     (SQS10)
```

Therefore, for **every** bounded face decomposition obtained from `(SQS7)`,
at least one tree-face term has value at least `delta/2` on its canonical
defect.  Since `||D_13||<=2`, that component satisfies

```text
max(||ell_12||,||ell_23||)>=delta/4.                       (SQS11)
```

If the compatible symmetry group contains an automorphism swapping the two
tree faces while fixing the closing face, average the splitting `(SQS7)` as
well as `ell`.  The two summands in `(SQS10)` are then equal, so **both** are
at least `delta/2` and both component norms are at least `delta/4`.

Finally, there is no larger independent parabolic averaging hidden here.
The common standard inner conjugations which preserve all three marked face
algebras factor through `P_0`; up to actual diagram automorphisms, the
available finite inner averaging is the common `P_0` action, not independent
`P_12`, `P_23`, and `P_13` actions.  Averaging over a single face group does
not preserve the other two face summands and therefore does not preserve the
comparison problem `(SQS2)`.

Proof: `symmetrize-separator-and-test-liftable-face-expectations`.

**What survives.**  The result does not rule out `(SQS2)` and does not prove
local splitting.  It rules out the hoped-for reduction to a functional of
one face, including the closing-face cyclic-holonomy witness, and proves that
every face decomposition retains a tree component of norm at least
`delta/4`.  Without an actual tree-swap symmetry it does not force both named
tree components separately; it forces at least one of them.

DERIVATION
symmetrize-separator-and-test-liftable-face-expectations
