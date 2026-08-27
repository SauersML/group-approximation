---
rg: 2
id: agent-free-compressor-fd-invisibility-proof
kind: route
title: Pass through the finite common-root coefficient quotient and its regular module
target: agent-free-compressor-full-corner-root-is-fd-invisible
requires:
  - agent-free-compressor-minimal-nonretractive-corner
---

For `(FCI1)` define

```text
K_rho={a in R_BCL:rho(x_ij(a))=1 for every i!=j}.      (FIP1)
```

Root additivity makes `K_rho` an additive subgroup.  Weyl conjugacy identifies
the root positions, and the Steinberg commutator formula with a spare index,

```text
[x_ij(a),x_jk(b)]=x_ik(ab),                            (FIP2)
```

closes `K_rho` under left and right multiplication.  Hence it is a two-sided
ideal.

The additive root image is finite.  Indeed it is an abelian exponent-`p`
subgroup of `U(d)`.  Its commuting normal matrices are simultaneously
diagonalizable, and every diagonal entry is a `p`-th root of unity, so the
group has at most `p^d` elements.  Therefore

```text
A_rho=R_BCL/K_rho                                     (FIP3)
```

is a finite ring.

Assume `rho(x_12(P_f))!=1`.  Then the image `bar P_f` is nonzero in
`A_rho`.  Let the finite ring act faithfully on its left regular vector
space over the splitting field `k`.

There is no packet-collapse loophole here.  The characteristic of `k` is
coprime to `|B_f|`, so Maschke's theorem gives

```text
k[B_f]=direct_sum_(lambda in Irr_k(B_f)) M_(d_lambda)(k). (FIP4)
```

The packet idempotent `P_f` is the sum of a fixed collection of primitive
central blocks, each chosen to have the Reynolds gap `(MNC2)`.  The kernel of
the homomorphism `k[B_f]->A_rho` is a two-sided ideal and therefore a sum of
whole blocks.  On every simple block under `P_f`, the restriction is either
zero or injective.  Since `bar P_f!=0`, at least one selected block survives,
and every surviving `P_f`-block retains its original `A_f/B_f` Reynolds
ranks.  Taking the minimum of their finitely many positive gaps gives the
same fixed `gamma>0` in the quotient.  If `P_f` is primitive, this reduces to
the statement that a nonzero homomorphism from the simple algebra
`P_f k[B_f]` is injective.

All relations `(BCL0)--(BCL2)` pass to the finite left regular coefficient
module.  In particular, the three row families of
`agent-free-compressor-minimal-nonretractive-corner` hold on the nonzero
corner `bar P_f A_rho`, while the selected packet Reynolds gap remains the
fixed positive gap `(MNC2)`.  That theorem forces `bar P_f=0`, a
contradiction.  Hence `P_f in K_rho`, proving `(FCI2)` in one root position;
Weyl conjugacy proves it in every position.
