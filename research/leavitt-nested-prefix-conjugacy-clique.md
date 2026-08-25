---
rg: 2
id: leavitt-nested-prefix-conjugacy-clique
kind: claim
title: Nested binary-Leavitt prefix roots form an infinite marked conjugacy-difference clique
distinct_from:
  binary-leavitt-cumulative-complete-graph-table: that uses cumulative rows and adjacent columns to make off-diagonal commutators trivial; this uses one nested idempotent root per vertex and makes every vertex difference conjugate to the marked root.
  leavitt-chromatic-tables-have-area-divergence: that freezes a column in the shift/cumulative commutator tables and obtains a forbidden centralizer section; no root is fixed along the present edge identities, so that argument does not decide their filling area.
  rf-conjugacy-difference-graphs-finitely-colorable: that forbids infinite chromatic conjugacy-difference graphs over residually finite actors; the binary-Leavitt elementary group has no nontrivial finite quotient, and this constructs an actual infinite clique.
artifacts:
  - research/leavitt-nested-prefix-conjugacy-clique-proof.md
---

Let `L=L_(F_2)(1,2)`, put `q=s_1t_1`, and work in `St_20(L)`.  For
`m>=0`, define the nested prefix idempotents and vertex roots

```text
e_m=s_(0^m)t_(0^m),             b_m=x_12(e_m).          (NPC1)
```

For every `j<k`, characteristic two and root additivity give

```text
b_j^(-1)b_k=x_12(e_j+e_k).                              (NPC2)
```

The coefficient `f_(j,k)=e_j+e_k` is a nonzero idempotent.  More precisely,

```text
f_(j,k)=sum_(ell=j)^(k-1)
          s_(0^ell 1)t_(0^ell 1).                      (NPC3)
```

It is Murray--von Neumann equivalent to `q`.  Choose any complete binary
prefix code of `k-j` leaves below the cylinder `1`, pair those leaves with
the `k-j` target leaves in `(NPC3)`, and sum the corresponding prefix partial
equivalences.  This gives `x,y in L` with

```text
yx=q,                         xy=f_(j,k).               (NPC4)
```

The stabilized elementary conjugator of
`murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness`, followed by a
fixed Weyl root permutation, therefore conjugates `x_12(f_(j,k))` to the
marked root

```text
z=x_13(q).                                               (NPC5)
```

Thus the complete graph on the vertices `{b_m:m>=0}` is an exact
conjugacy-difference code for `z`, and has infinite chromatic number.

This is an algebraic clique only.  The standard proof of `(NPC4)` uses
`k-j` prefix leaves, and the finite-presentation area of `(NPC2)--(NPC5)` is
not shown to be uniform.  The quantitative question is isolated in
`leavitt-nested-prefix-conjugacy-uniform-area`.

DERIVATION
leavitt-nested-prefix-conjugacy-clique-proof
