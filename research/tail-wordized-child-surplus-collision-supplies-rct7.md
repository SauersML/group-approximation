---
rg: 2
id: tail-wordized-child-surplus-collision-supplies-rct7
kind: claim
title: One tail-wordized child-surplus collision supplies the strict recursive exposure
distinct_from:
  recursive-clifford-tail-supplies-anchor-but-not-contraction: that constructs the same-gauge identity-outer tail and leaves the strict payload exposure as RCT7; this supplies RCT7 from Schur violation surplus and one returned projection collision.
  schur-violation-density-gives-contraction: that derives contraction after an abstract next-carrier inequality; this derives that inequality from one ordinary reflection conjugacy and proves exact HNN completeness.
  reset-schur-bcs-branching-atlas: that asks for a full recurrent corrected-center atlas; this reduces its non-type-preserving return to one tail-wordized child reflection and one support-leakage row.
  exact-first-hit-ladder-kills-regular-carrier: that rules out a trace-functorial positive exit at every level; here the exact perfect model has zero violation surplus, while only finite matrices have the positive BCS surplus.
---

**ESTABLISHED SUFFICIENT CELL.**  A recursive Clifford tail turns the
corrected Schur child-center reflection into an ordinary word.  One HNN
conjugacy from that word to the next baseline-carrier reflection then converts
the finite-dimensional forbidden BCS mass directly into the strict factor
`lambda<1` required by `(RCT7)`.

## The matrix collision lemma

Let `(M_d,tr)` be a normalized matrix algebra.  At level `n`, let

```text
Q_n = current baseline carrier,       a_n=tr(Q_n),
v_n = sum of context-forbidden masses,
C_n = full violation-oriented child,  c_n=tr(C_n),
Q_(n+1) = next baseline carrier,       a_(n+1)=tr(Q_(n+1)). (TSC1)
```

Only the scalar sum `v_n` and the trace of `C_n` are used; the forbidden
projections may belong to different noncommuting BCS contexts.  Suppose local packet
exactification and the robust shared-BCS gap give

```text
v_n>=beta a_n-delta_n,                                (TSC2)
c_n>=a_n+v_n-xi_n.                                    (TSC3)
```

Here `(TSC3)` is the violation-oriented Schur child identity: every old copy
reproduces once and every forbidden copy contributes one surplus child.

Let `U_n` be a unitary return word and put

```text
ell_n=||(1-Q_(n+1))U_n C_n||_2^2.                     (TSC4)
```

Trace cyclicity gives

```text
ell_n
 =c_n-tr(Q_(n+1)U_nC_nU_n^*)
 >=c_n-a_(n+1).                                       (TSC5)
```

Consequently `(TSC2)--(TSC5)` imply

```text
(1+beta)a_n<=a_(n+1)+delta_n+xi_n+ell_n,
a_n<=lambda a_(n+1)
     +lambda(delta_n+xi_n+ell_n),
lambda=(1+beta)^(-1)<1.                               (TSC6)
```

This is exactly `(RCT7)`, with no first-hit reservoir and no selection of an
individual forbidden context.

## One ordinary relator controls the collision

Assume the recursive tail packet wordizes the two carrier reflections

```text
R_(C,n)=1-2C_n,             R_(Q,n+1)=1-2Q_(n+1).      (TSC7)
```

For the child reflection, this is the point of the identity-outer anchor:
the semantic Clifford implementer `T_n=CZ_n tensor V_n` multiplied by its
child-tail anchor `A_n=I tensor V_n` is the literal corrected-center gate
`CZ_n tensor I`.  No multiplicity twist remains.

Add the single ordinary conjugacy relator

```text
r_n=R_(Q,n+1) U_n R_(C,n) U_n^*=1.                    (TSC8)
```

The reflection identity gives

```text
ell_n<=1/4 ||r_n-1||_2^2.                              (TSC9)
```

Indeed

```text
(R_(Q,n+1)U_n-U_nR_(C,n))C_n
       =2(1-Q_(n+1))U_nC_n.                           (TSC10)
```

Thus if the level-`n` words and derivations have polynomial cost `p(n)` from
the Thompson/recursive tape, then for global squared relator energy `E<=1`,

```text
delta_n+xi_n+ell_n<=K p(n)sqrt(E).                    (TSC11)
```

Equations `(TSC6)` and `(TSC11)` feed
`contractive-computation-ladder`, including its positive-density-level
version.  A fixed marked floor at level zero therefore forces a
dimension-independent positive lower bound on `E`.

## Why stationary Clifford packets now fail

The finite-depth stationary model from the recursion-only audit can keep
`a_(n+1)=a_n`, but if the shared BCS tuple has forbidden mass `v_n`, then
`(TSC3)--(TSC5)` force

```text
ell_n>=v_n-xi_n.                                       (TSC12)
```

Hence a positive forbidden fraction cannot circulate as a stationary type
flow after `(TSC8)` is installed.  It pays the support relator.  This is the
payload-dependent collision absent from the affine clone and finite
Clifford-graph countermodels.

The word **shared** remains load-bearing.  Replacing `(TSC2)` by one scalar
classical-unsatisfiability bound on independent context copies reopens the
virtually-free stationary model.  The robust BCS gap must be applied to one
globally shared approximate tuple before its forbidden mass is routed through
the child packet.

## Exact completeness and Britton embedding

Let the fixed BCS have a perfect tracial model with no Connes-embeddable
trace.  In that model all forbidden projections vanish, so

```text
v_n=0,             c_n=a_n.                            (TSC13)
```

Use countable amplification at every level.  The `+/-` eigenspaces of
`R_(C,n)` and `R_(Q,n+1)` then have matching infinite multiplicities; after
adding an infinite spectator to any zero complement, they are unitarily
conjugate.  Choose `U_n` implementing that conjugacy.  The recursive tail
model supplies `(TSC7)` exactly, so `(TSC8)` holds with zero error and the
marked BCS representation survives.

Algebraically, adjoin `U_n` as an HNN stable letter identifying the two
order-two subgroups generated by `R_(C,n)` and `R_(Q,n+1)`.  Provided the two
reflection words are nontrivial in the base packet, Britton's lemma embeds
the base.  Thus the marked word is not killed by the collision relator.  A
single shift/Thompson template may generate all levels; its addressed word
and derivation cost are polynomial in `n`.

This proves exact compatibility and the full scalar soundness implication.
The remaining presentation-level obligation is sharply syntactic: realize
the recursive tail gates and the aggregate corrected Schur child reflection
as the promised finite word template while keeping the shared BCS contexts
noncommuting.  No additional analytic contraction, determinant, first-hit
budget, or multiplicity-index theorem is required after that wordization.

The existing Schur--Toeplitz envelope does not yet discharge this obligation.
`schur-toeplitz-head-swap-exposes-the-steinberg-injectivity-fork` repairs the
head swap over the required odd splitting field and proves finite generation
over the recursive tail.  It also isolates the exact remaining fork:
`EL_5(R_f)` has the faithful coefficient shift but no proved finite
presentation, while `St_5(R_f)` is finitely presented but injectivity of
`St_5(sigma)` is open.  Moreover its torus word reflects the raw defect
`sigma^n(P_f)`, not yet the aggregate corrected child `C_n` in `(TSC3)`.
Thus the smallest algebraic target is Steinberg shift injectivity, followed
by one coefficient identity realizing the corrected-child reflection.
