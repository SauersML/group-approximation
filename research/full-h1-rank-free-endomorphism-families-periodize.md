---
rg: 2
id: full-h1-rank-free-endomorphism-families-periodize
kind: claim
title: Full-H1-rank free endomorphism families share marked periodizations
distinct_from:
  single-free-endomorphism-has-marked-finite-quotients: that handles one arbitrary injective free-group endomorphism through mapping-torus residual finiteness; this handles any finite family simultaneously under the explicit full-rank abelianization hypothesis.
  coprime-power-pair-phase-hnn-is-residually-finite: that constructs characteristic finite p-group quotients for one two-coordinate power-pair HNN and separates every whole-group word; this constructs one common marked base quotient for arbitrary finite families of free-group endomorphisms with nonsingular H1 maps.
  abelian-matrix-hnns-have-marked-finite-quotients: that reduces integer matrices acting on `Z^n`; this lifts the same determinant screen to nonabelian free groups using their free pro-p completions.
---

ESTABLISHED.  Let `F_n` be a finite-rank free group and let

```text
phi_1,...,phi_r:F_n->F_n                               (FHR1)
```

be endomorphisms whose maps on integral abelianization have nonzero
determinant.  For every `1!=y in F_n`, there is a finite `p`-group quotient

```text
q:F_n->Q,                  q(y)!=1,                    (FHR2)
```

on which every `phi_i` descends to an automorphism.

Choose a prime `p` which divides none of the finitely many determinants.
The free group is residually `p`, so its image in the free pro-`p` completion
`P` still contains `y` nontrivially.  Each `phi_i` extends continuously to
an endomorphism of `P`.  Its action on

```text
P/Phi(P) ~= H_1(F_n;F_p)                               (FHR3)
```

is invertible.  The pro-`p` Burnside basis theorem therefore makes the
extension an automorphism of `P`.

Choose an open normal subgroup `U` of `P` not containing `y`.  A finitely
generated pro-`p` group has only finitely many open subgroups of each bounded
index.  Intersect all open subgroups of index at most `[P:U]`; the result `C`
is open, characteristic, and contained in `U`.  Hence

```text
Q=P/C                                                    (FHR4)
```

is finite, detects `y`, and every `phi_i` induces an automorphism of `Q`.

In particular the multiple ascending presentation

```text
<F_n,t_1,...,t_r |
  t_i g t_i^(-1)=phi_i(g)>                              (FHR5)
```

maps to the finite group `Q rtimes <bar phi_1,...,bar phi_r>` with the mark
alive.  Thus several noncommuting/nonamenable branches do not help when all
their `H_1` maps have full rational rank.

Combined with `single-free-endomorphism-has-marked-finite-quotients`, the
only free-group boundary not covered here is a genuinely multi-branch family
containing at least one injective endomorphism singular on rational
abelianization.  Such a family must fail to share the periodic points which
Borisov--Sapir construct separately for each branch; merely being proper or
nonabelian is insufficient.
