---
rg: 2
id: leavitt-chromatic-tables-have-area-divergence
kind: claim
title: The shift and cumulative Leavitt chromatic tables contain fixed-mark centralizer sections of divergent area
distinct_from:
  binary-leavitt-shift-graph-has-exact-marked-commutator-table: that proves every displayed edge commutator is exactly trivial; this proves their filling areas cannot be uniformly bounded.
  binary-leavitt-cumulative-complete-graph-table: that proves the exact complete table by characteristic-two cancellation; this freezes one column and applies finite-mark centralizer properness to its infinitely many rows.
  level-synchronous-first-mismatch-area-is-centralizer-impossible: that treats the stabilized Morita branch tree after normalizing a moving column; the two tables here already contain a fixed column and need no normalization.
---

**ESTABLISHED.**  In every finite presentation of the stabilized
binary-Leavitt Steinberg group, the exact shift-graph and cumulative
complete-graph tables have unbounded edge filling area.

For the shift graph, fix the vertex `v=(0,1)`.  Its word

```text
beta=h_v=x_23(S_0+S_1)                                  (CLD1)
```

is a fixed nontrivial involution.  For every `k>=2`, the vertex `w_k=(1,k)`
is an outgoing neighbor and

```text
eta_k=c_(w_k)=x_12(T_k),          [eta_k,beta]=1.        (CLD2)
```

The `eta_k` occupy infinitely many distinct cosets modulo `<beta>`: their
coefficients are distinct, and the elementary matrix quotient separates the
`x_12` root subgroup from the `x_23` subgroup containing `beta`.  Therefore

```text
sup_(k>=2) Area([eta_k,beta])=infinity.                 (CLD3)
```

For the cumulative table, choose one infinite orthogonal corner sequence and
use its initial segments.  Freeze

```text
beta'=h_0=x_23(B_0+B_1).                                (CLD4)
```

For every `k>=1`, characteristic two gives

```text
C_k(B_0+B_1)=q+q=0,
[c_k,beta']=1.                                          (CLD5)
```

The cumulative coefficients `C_k` are distinct, so the same elementary-root
argument puts the `c_k` in infinitely many cosets modulo `<beta'>`.  Hence

```text
sup_(k>=1) Area([c_k,beta'])=infinity.                  (CLD6)
```

Both conclusions are immediate from
`finite-mark-centralizer-commutator-area-is-proper`.  Exact coefficient
cancellation and infinite chromatic number remain valid; what fails is
precisely the bounded presentation-area upgrade required by `(CCC2)`.
