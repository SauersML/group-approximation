---
rg: 2
id: agent-first-hit-fresh-copy-reynolds-tree-is-contractive
kind: claim
title: A fresh-copy Reynolds tree transports rejection mass but does not create persistent carrier mass
distinct_from:
  exact-first-hit-ladder-kills-regular-carrier: that rules out an exact trace-functorial persistent infinite ladder in the canonical trace; this computes the finite-depth recurrence actually produced when each fresh BCS copy lives only on the preceding exit layer.
  independent-address-capacity-cannot-drive-selected-atom-growth: that proves a Kraft bound for address cylinders; this identifies the earlier failure that occurs even before address capacity is considered.
  role-packed-bcs-gap-is-one-idempotent: that constructs one positive forbidden source inside a given carrier; this shows that exact HNN transport of that source produces a smaller next active carrier, not a larger one.
---

**ESTABLISHED.**  Consider one level of a finite fresh-copy construction.  Let
`Q_n` be the orthogonal union of the active node carriers at depth `n`.  On
each node install one shared structural BCS tuple and role-pack its forbidden
Reynolds atoms.  Write the resulting pairwise orthogonal source projections as

```text
A_(n,1),...,A_(n,r_n) <= Q_n.                         (FCT1)
```

Transport every source by an index-two finite-subgroup HNN row to pairwise
orthogonal target character atoms

```text
D_(n,i)=U_(n,i) A_(n,i) U_(n,i)^*,                   (FCT2)
Q_(n+1)=sum_i D_(n,i),                                (FCT3)
```

and put the fresh shared BCS tuples for depth `n+1` on `Q_(n+1)`.  In every
exact finite-dimensional representation,

```text
q_(n+1):=tau(Q_(n+1))
          =sum_i tau(A_(n,i)) <= tau(Q_n)=:q_n.        (FCT4)
```

The role-packed robust BCS gap supplies only the reverse lower estimate

```text
c q_n-C sqrt(E) <= q_(n+1),             0<c<=1,       (FCT5)
```

where `c=beta/m` for the equal role packet.  Thus the active recurrence is
contractive:

```text
c q_n-O(sqrt(E)) <= q_(n+1) <= q_n+O(sqrt(E)).         (FCT6)
```

It is not the persistent first-hit recurrence.  Even if carriers belonging to
different depths are separately authenticated as orthogonal, the available
conclusions are only

```text
sum_(j<N) q_j <=1,
q_j >=c^j q_0-O_j(sqrt(E)),                            (FCT7)
```

and hence

```text
q_0 sum_(j<N)c^j <=1+O_N(sqrt(E)).                    (FCT8)
```

For `c<1` the left side stays bounded as `N` grows.  Freshness has not
regenerated the baseline part of `Q_n`; HNN conjugacy has merely moved the
selected rejection mass without changing its trace.

Keeping the old layers in a cumulative carrier

```text
C_n=Q_0+...+Q_n                                       (FCT9)
```

does not repair `(FCT5)`: a BCS tuple installed only on the new layer has a
gap proportional to `q_n`, not to `tau(C_n)`.  Installing a fresh BCS tuple on
all of `C_n` instead requires the new target to lie outside the very carrier
on which its source is selected.  Finite character addresses cannot certify
that without charging the same capacity to the old carrier: disjoint address
cylinders obey the Kraft inequality in
`independent-address-capacity-cannot-drive-selected-atom-growth`.

Therefore a finite first-hit tree of fresh copies does not supply a
supercritical cumulative carrier.  To do so one still needs a genuinely
payload-sensitive return/escape relation that preserves the old active
carrier while placing an equal-rank copy of its selected projection outside
it.  That is the original groupification gate, not an effect of using fresh
BCS copies.

DERIVATION
agent-first-hit-fresh-copy-reynolds-tree-is-contractive via agent-first-hit-fresh-copy-reynolds-tree-accounting

