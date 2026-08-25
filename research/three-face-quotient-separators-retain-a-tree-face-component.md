---
rg: 2
id: three-face-quotient-separators-retain-a-tree-face-component
kind: claim
title: Symmetrized three-face quotient separators retain an essential tree-face component
distinct_from:
  exhausting-ideal-reservoirs-have-lift-or-quotient-separator: that produces an abstract quotient-level separator when exhausting reservoir distance stays positive; this analyzes such a separator on the concrete three-face system and proves that symmetry averaging cannot concentrate it on one face.
  explicit-finite-face-ucp-section-is-edge-equivariant: that constructs a ucp section on the closing finite face; this uses that section, after the subgroup Fourier expectation, to rule out every closing-face-supported separator.
  three-face-ucp-balancing-needs-macroscopic-tree-motion: that gives a positive Gram obstruction to canonical tree-face values; this is a dual-functional normal form showing that the same closing-face Gram cycle cannot by itself be a quotient nonliftability separator.
  equal-difference-gram-averaging-fails-at-four-free-words: that shows truncated equal-difference averaging need not preserve positivity; this averages a linear separator only over genuine compatible automorphisms, for which the ucp comparison class is invariant.
---

**ESTABLISHED (scoped averaging no-go).**  In the explicit `(3,3,4)`
Kac--Moody triangle put

```text
A=C^*(G_0),       Q=C^*(Lambda),
S_Delta=C^*(P_12)+C^*(P_23)+C^*(P_13) subset Q,
q:A->>Q.                                                    (SQS1)
```

Suppose a bounded real functional `ell` on the self-adjoint map space
`L_sa(S_Delta,Q)` is a quotient separator of the type supplied by `(ERD3)`:

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

be the subgroup Fourier expectation, restricted to `S_Delta`.  It is ucp,
and `M_H|_(C^*(H))=id`.  Moreover `M_H` is liftable through `q`:

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

There is a useful finite normal form.  Since `S_Delta` is the vector-space
sum of its three face algebras, every bounded functional on its map space can
be written

```text
ell(psi)=ell_12(psi|_(C^*(P_12)))
        +ell_23(psi|_(C^*(P_23)))
        +ell_13(psi|_(C^*(P_13))),                         (SQS7)
```

with the usual nonuniqueness on face intersections.  An `Omega`-invariant
separator admits an equivariant such decomposition by averaging a
decomposition.  Equation `(SQS6)` says that no decomposition can have only
one essential face term.  At the `(3,3,4)` diagram every diagram symmetry
fixes the unique type-`4` face `P_13` and at most swaps `P_12` with `P_23`.
Thus a symmetrized separator has the normal form

```text
closing-face term + symmetric (or separately invariant) tree-face terms,
```

and at least one tree-face term is essential.  This is the component that the
one-face Boca/finite-section construction does not control.

Finally, there is no larger independent parabolic averaging hidden here.
The common standard inner conjugations which preserve all three marked face
algebras factor through `P_0`; up to actual diagram automorphisms, the
available finite inner averaging is the common `P_0` action, not independent
`P_12`, `P_23`, and `P_13` actions.  Averaging over a single face group does
not preserve the other two face summands and therefore does not preserve the
comparison problem `(SQS2)`.

Proof: `symmetrize-separator-and-test-liftable-face-expectations`.

**What survives.**  The result does not rule out `(SQS2)` and hence does not
prove local splitting.  It rules out the hoped-for one-face reduction and
isolates the remaining dual object: a symmetry-invariant, genuinely
multi-face functional coupling at least one tree-face order to the closing
face.  Any contradiction must control that transverse component, not merely
the finite kernel-cycle Gram matrix.

DERIVATION
symmetrize-separator-and-test-liftable-face-expectations
