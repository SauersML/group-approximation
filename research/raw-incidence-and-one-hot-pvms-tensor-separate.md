---
rg: 2
id: raw-incidence-and-one-hot-pvms-tensor-separate
kind: claim
title: Exact raw incidence and exact one-hot chart PVMs can remain tensor-separated
distinct_from:
  two-equivariant-shell-pvms-have-independent-coordinate-escape: that separates two covariant shell PVMs but omits the raw denominator branch system; this adjoins an exact raw branch PVM and every section identity while leaving the decoded deficit unchanged.
  raw-denominator-incidence-kills-off-diagonal-shell-orbit: that kills off-diagonal mass when the compared projections are the raw branch conjugates themselves; this proves that independently decoded one-hot atoms need not couple to those raw conjugates at all.
  every-fixed-hecke-window-retains-graph-product-nonedges: that uses the native infinite graph-product model and compatible clique Fourier PVMs; this is a finite-dimensional three-coordinate counterpacket with complete one-hot PVMs in both charts.
---

Let `Omega` be a transitive finite `G`-set of size `q>=2`, fix `o in Omega`,
and work on

```text
H=l^2({0,1}^Omega_raw x Omega_1 x Omega_2).            (RIO1)
```

Let `G` act by the Bernoulli coordinate permutation on the first factor and
diagonally on the other two. On the first coordinate put the balanced raw
branch projections

```text
A_i=B_i=1_(xi_i=1).                                    (RIO2)
```

Choose sections `a_i,b_i in G` and corrections `d_i in Stab_G(o)` with
`a_i=b_i d_i` and `a_i o=b_i o=i`. For the base projection
`R=1_(xi_o=1)`, this gives the literal raw incidence identities

```text
a_i R a_i^*=b_i R b_i^*=A_i=B_i,       [R,d_i]=0.      (RIO3)
```

Thus every raw section-word error and the complete raw authentication
deficit vanish, while every `A_i=B_i` has the native balanced trace `1/2`.

On the other two coordinates put the decoded chart PVMs

```text
P_i=1_(x_1=i),                 Q_i=1_(x_2=i).           (RIO4)
```

They are complete, equal-rank, and exactly covariant under the same diagonal
`G`-action. Moreover the involutions

```text
u_i=I-2P_i,                    v_i=I-2Q_i              (RIO5)
```

form exact commuting one-hot packets: their joint Fourier PVMs have only the
`q` sign patterns with exactly one negative coordinate nonzero, and those
atoms are precisely `(P_i)` and `(Q_i)`. Hence every within-chart
one-hot/Fourier identity, moment identity, and actor-covariance row is exact.

Nevertheless normalized trace gives

```text
tau(P_i)=tau(Q_i)=1/q,         tau(P_iQ_i)=1/q^2,
Delta=(1/2)sum_i||P_i-Q_i||_2^2=1-1/q.                 (RIO6)
```

For the arithmetic value `q=42`, the cross-chart saturation deficit is
`41/42` although all separate raw-incidence and one-hot/Fourier energies are
zero. Therefore no inequality can bound `Delta` using only those two
families of defects, even in finite matrices with exact equal ranks and a
common actor representation.

The first mixed term which sees the counterpacket is exactly the atomwise
section leakage from `equal-rank-denominator-edges-authenticate-decoded-atoms`.
The raw transition `T_i=b_i^*a_i=d_i` only permutes atoms inside each
decoded coordinate. Since the two coordinates remain independent, for any
prescribed target relabeling `sigma(i)`,

```text
sum_i ||(1-Q_(sigma(i)))T_iP_i||_2^2
 =sum_i (1/q-1/q^2)
 =1-1/q=Delta.                                         (RIO7)
```

Thus `(EDA11)` is not dispensable bookkeeping and cannot be inferred from
raw incidence plus separate Fourier decoding. A successful arithmetic
decoder must prove that these genuinely mixed atomwise section leakages are
paid by its conductor/root ledger. Once that is done, `(EDA13)` supplies
the desired five Gram saturations.
