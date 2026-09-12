---
rg: 2
id: arity-imbalanced-schur-heads-have-a-stationary-exit
kind: claim
title: An arity-imbalanced Schur head labels an exit but does not pay for it
distinct_from:
  binary-schur-head-embeddings-are-relative-inner-holonomies: that classifies the full-block maps into an arbitrary number of equal children; this proves the resulting ternary two-return/one-exit recurrence is either not an ordinary unital group-word wire or has a zero-defect regular stationary escape.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that supplies the regular stationary vector for every finite restriction graph; this applies it to the proposed arity-imbalanced recurrence and separates a literal two-thirds rank identity from a one-sided payment inequality.
  approximate-relative-leavitt-cell-kills-active-trace: that obtains a genuine trace payment from decoded nonunitary Leavitt coefficient equations; this shows that changing the number of Schur children does not provide the missing group-word decoder.
---

Let `k` be a splitting field and let the marked parent sector be the full
matrix algebra

```text
A=M_n(k).
```

Consider a proposed `m`-child Schur head whose marked part is `A^m`.  There
are only two ways to interpret an `r`-return/`(m-r)`-exit wire using ordinary
group words, and neither gives a paid exit.

First suppose the wire is a unital algebra map

```text
psi:A -> A^m.                                             (ASE1)
```

Every coordinate of `psi` is a unital endomorphism of `A`, hence is an inner
automorphism.  Thus

```text
psi(a)=(u_1 a u_1^-1,...,u_m a u_m^-1),                  (ASE2)
```

and all `m` children are faithful copies of the parent.  In particular there
is no unital `L(1,3)` Schur-head map that returns two full branches and sends
the third to zero or to the augmentation.  A stable-letter relation between
the corresponding packet subgroups compares the **whole** restricted module
and therefore also returns the third coordinate.

The alternative is to enlarge the finite packet and relabel one or more
nonzero target types as exits.  Suppose for clarity that `m=3`, a branch
permutation packet acts transitively, and its three orthogonal central packet
projections are `q_0,q_1,q_2`, with

```text
q=q_0+q_1+q_2,       q_ret=q_0+q_1,       q_exit=q_2.    (ASE3)
```

In every exact representation of the branch-permutation packet,

```text
tr(q_ret)=2 tr(q)/3,             tr(q_exit)=tr(q)/3.     (ASE4)
```

Equation `(ASE4)` is a rank identity, but it is not a contraction recurrence:
the missing third has merely been moved to the exit type.  For any finite
network of such packet-subgroup wires, choose the positive regular stationary
type vector of `finite-packet-graph-atlases-have-a-regular-stationary-flow`.
All restriction and stable-letter matching defects are exactly zero, while
every nonzero exit type has positive multiplicity.  If branch symmetry is
retained, the exit carries exactly the last third in `(ASE4)`; without branch
symmetry its multiplicity is unconstrained and can only be harder to charge.

Consequently no dimension-independent estimate

```text
tr(q_exit) <= C E                                      (ASE5)
```

can follow from these finite packet and restriction relations, where `E` is
any sum of their normalized-Hilbert--Schmidt group-word defects.  The regular
stationary representation has `E=0` and `tr(q_exit)>0`.  Direct sums preserve
zero defect, and amplification preserves both normalized traces in `(ASE4)`,
so the obstruction is amplification-stable.

One might try to turn `(ASE4)` into a recurrence by adjoining a unitary that
conjugates the parent carrier onto `q_ret`.  That is not supplied by the
arity-three head.  On projections it is the extra relation

```text
t q t^-1=q_ret,                                        (ASE6)
```

which is impossible in a finite-dimensional representation with
`tr(q)>0`, because conjugacy preserves rank and `(ASE4)` does not.  Moreover
`q` and `q_ret` are group-algebra projections, not ordinarily group elements,
so `(ASE6)` is not itself a group relator.  Replacing them by reflection words
does not come for free: a nonidentity involution in a finite group's regular
representation has negative spectral rank exactly one half, and therefore
cannot name a two-thirds subcarrier.  Any gadget that really groupifies
`(ASE6)` and controls its approximate matrix models has supplied the missing
one-sided payment mechanism rather than obtained it from arity imbalance.

The same proof works for every `1<=r<m`: a transitive `m`-branch packet gives
the formal proportions `r/m` and `(m-r)/m`, but the omitted mass is a positive
stationary type at zero defect.  A properly infinite marked representation
may absorb `m` copies and hence supplies completeness, but proper infiniteness
does not alter this finite-matrix soundness obstruction.

Thus `L(1,3)` does not bypass the Atlas/Fanizza gate.  The only known genuine
arity payment remains the nonunitary trace identity in
`approximate-relative-leavitt-cell-kills-active-trace`; exposing its
coefficient contractions with ordinary group words is still the decoder
problem.
