---
rg: 2
id: role-packed-bcs-gap-is-one-idempotent
kind: claim
title: A finite spin role packet turns the whole BCS gap into one fixed idempotent
distinct_from:
  maximal-forbidden-atom-has-a-named-positive-half: that chooses a representation-dependent maximal forbidden type; this keeps every type simultaneously in one fixed orthogonal aggregate.
  role-multiplexing-is-minimax-max-selection: that proves the abstract minimax trace bound for arbitrary role weights; this applies the equal-spin packet to the robust shared BCS gap and obtains one reusable payload idempotent.
  finite-adaptive-selected-atom-ring-tree: that branches over every possible maximal type; this makes the coefficient tree unary at the cost of the same fixed inverse-menu factor.
---

**ESTABLISHED.**  Fix the shared non-CE BCS, enumerate its `M` forbidden
assignment projections as `P_1,...,P_M`, and let its robust carrier gap be

```text
sum_i tau(QP_i)>=beta tau(Q)-C_B sqrt(E).              (RBG1)
```

Choose `k` with `m=2^k>=M`.  Adjoin an extraspecial `2`-group role packet
with central involution identified with the BCS mark `J`, and require every
shared BCS generator to commute with the packet.  On the `J=-1` sector the
packet has its unique `m`-dimensional spin type.  Let

```text
R_1,...,R_M
```

be distinct joint atoms of one maximal diagonal Pauli subgroup and put

```text
B_f=sum_(i=1)^M R_i P_i.                               (RBG2)
```

Then `B_f` is one fixed rational group-algebra projection.  In every exact
finite-dimensional representation, and on every projection `Q<=Q_-` which
reduces both the full role packet and the shared BCS tuple,

```text
tau(QB_f)=m^(-1) sum_i tau(QP_i).                      (RBG3)
```

Consequently every sufficiently accurate canonical matrix microstate,
after fixed packet correction and commutant averaging, satisfies

```text
tau(QB_f)>=(beta/m)tau(Q)-C_f sqrt(E).                 (RBG4)
```

All cross-context products disappear from `(RBG2)`: the factors `R_i`
make the summands orthogonal even when `P_iP_j!=P_jP_i`.  No maximal-type
choice and no arbitrary-list SELECT word remain.

The construction preserves exact tracial completeness.  Tensor the perfect
BCS model with the unique spin representation.  Every forbidden `P_i` is
zero, hence

```text
B_f=0.                                                 (RBG5)
```

Thus any later relation conditional on the aggregate source is vacuous in
the perfect model while `J=-1` survives.

The factor `1/m` is optimal among independent finite role packets by
`role-multiplexing-is-minimax-max-selection`; this claim is a syntax and
coherence reduction, not a quantitative amplification.  Its useful output
is that `finite-adaptive-selected-atom-ring-tree` may be replaced by a unary
finite coefficient ladder.  At level `n`, use the single source

```text
a_n=q_n B_f,                                           (RBG6)
```

adjoin one Murray--von Neumann arrow from `a_n` to
`d_n orthogonal q_n`, and put `q_(n+1)=q_n+d_n`.  In an exact finite
star-representation,

```text
tau(q_(n+1))=tau(q_n)+tau(a_n)
             >=(1+beta/m)tau(q_n).                    (RBG7)
```

Starting at the Pauli quarter carrier and staying below `Q_-`, any fixed
depth with `(1+beta/m)^N>2` is contradictory.  The remaining issue is only
the normalized-HS decoding of this unary conditional ladder from ordinary
Steinberg group microstates.  In particular, there is no longer a common
orientation problem among several outgoing types at one parent.

DERIVATION
role-packed-bcs-gap-is-one-idempotent via role-packed-bcs-gap-proof

