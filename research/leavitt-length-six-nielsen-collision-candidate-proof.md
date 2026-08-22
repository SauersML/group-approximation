---
rg: 2
id: leavitt-length-six-nielsen-collision-candidate-proof
kind: route
title: Move one root packet into the idle negative slot and collide the two formal copy-one gates
target: leavitt-length-six-nielsen-collision-candidate
requires:
  - leavitt-length-six-three-gate-weight-survivor
  - leavitt-three-gate-candidate-is-injective
---

## The deliberate modification

Keep the sign sequence `++++--`, the sign-change coefficients `a,e`, and the
permutation packet `p` in exactly the same positions as in the three-gate
candidate.  Change only the slots occupied by `q` and the final identity:

```text
(a,1,q,p,e,1)  --->  (a,1,a,p,e,q).                 (NC1)
```

Thus the new equation is

```text
W_col = a t^2 a t p t e t^(-1) q t^(-1),            (NC2)
q=x_34(s_1)x_(11,12)(t_0).
```

This is the smallest nontrivial gate collision obtainable while keeping the
three fixed packets `a,p,e` in place.  Indeed the two copy-one gate labels in
the second Reidemeister--Schreier relator are `k_0=A_1` and
`k_1=B_0C_1`.  Equality `k_1=k_0` in the free product `G_0*G_1` forces
`B=1` and `C=A`.  Replacing `q` by `a` would lose the `q` packet, so retaining
full support forces `q` into the only idle slot `F=1`.  Hence exactly the two
slot changes in `(NC1)` are necessary.  This is a designed equality in the
Nielsen table, not a word search.

## Full support and nonsingularity are unchanged

The nonidentity coefficient set of `(NC2)` is still exactly

```text
{a,q,p,e}.
```

The generation calculation in
`leavitt-length-six-three-gate-weight-survivor-proof` therefore applies
without alteration: selective Steinberg commutators split the two factors of
`q`, powers of `p` move all four Leavitt labels around the 20-cycle, and the
four packets generate `EL_20(L_(F_2)(1,2))`.

The total `t`-length is six and the exponent sum is
`1+1+1+1-1-1=2`.  The two cyclic sign changes still occur at `a` and `e`,
both nontrivial involutions.  Thus the packet move preserves the exact
features which placed the preceding word outside the generic short
torsion-free arguments.

The specialization `t=1` gives `a^2peq=peq`, which is not the identity.
Indeed `p` has an off-diagonal constant entry in every row.  Right
multiplication by `e` and the two factors of `q` changes only columns
`2,4,12`; choose a row other than row 1 whose `p`-entry is outside those
three columns.  Left multiplication by `a` does not change that row, so the
off-diagonal entry survives.

## Exact paired rewrite and atlas kernel

For general slots `(A,B,C,D,E,F)` of sign type `++++--`, the paired relators
are

```text
R_0=A_0B_1 z C_0D_1 z E_0 z^(-1)F_1,
R_1=A_1 z B_0C_1 z D_0E_1F_0 z^(-1).                (NC3)
```

Substitution from `(NC1)` gives

```text
R_0=a_0 z a_0p_1 z e_0 z^(-1)q_1,
R_1=a_1 z a_1 z p_0e_1q_0 z^(-1).                   (NC4)
```

Starting at the first occurrence of `z`, the corner labels are

```text
h_0=q_1a_0,   h_1=a_0p_1,   h_2=e_0,
k_0=a_1,      k_1=a_1,      k_2=p_0e_1q_0.           (NC5)
```

Let `Q_atlas` be the formal local corner group before imposing Leavitt
identities.  In particular its formal copy-one gate subgroup is

```text
<k_0,k_1 | k_0^2=k_1^2=[k_0,k_1]=1> = V_4.
```

The natural corner map `Q_atlas -> G_0*G_1` sends both formal generators to
the same nontrivial involution `a_1`.  Therefore

```text
k_0 k_1 != 1 in Q_atlas,       k_0 k_1 |-> a_1^2=1.  (NC6)
```

So the first Nielsen map genuinely fails injectivity.  This is precisely the
failure mechanism absent from the fenced candidate: its four possible
same-copy merges were nonidentity, whereas `(NC6)` is a length-two exact
coefficient face on which a gate corridor may terminate.

The lightweight artifact recomputes `(NC3)--(NC6)` directly from the prefix
heights.  No finite quotient or truncated Leavitt model enters the check.

## Honest frontier

The collision proves that the Nielsen--amalgam proof of
`leavitt-three-gate-candidate-is-injective` cannot transfer to `(NC2)`.  It
does **not** by itself prove that either coefficient copy dies in the paired
quotient.  After folding `k_0=k_1`, the second relator becomes

```text
a_1 z a_1 z (p_0e_1q_0) z^(-1)=1,
```

and a new normal-form or picture analysis is required.  The next exact test
is whether the new two-edge coefficient face can close a corridor with outer
boundary in one coefficient copy.  Calling `(NC2)` a KL counterexample
before that test would be unjustified.

That test is continued in
`leavitt-nielsen-collision-has-a-hidden-first-side-relation`.
After folding the duplicate gate, a disjoint-root commutator gives a genuine
long kernel in the first edge map, but a complete four-cell audit still finds
no coefficient-boundary disk.  The first-edge kernel has the wrong pushout
variance to imply a KL violation on its own.
