---
rg: 2
id: nand-triangle-relative-k1-is-a-finite-packet-index
kind: claim
title: The S4 NAND relative K1 is the finite-packet atom-difference index
distinct_from:
  s4-nand-cycle-holonomy-is-one-s2-bit: that computes the discrete plus-sheet permutation after coordinate matchings; this identifies its relative K1 boundary as the difference of the two plus-atom K0 classes.
  odd-nand-phase-return-has-exact-finite-models: that exhibits one exact signed-permutation model with visible phase; this shows that the nonzero relative index is already a finite-packet index while the central phase contributes no additional class.
  bass-serre-algebraic-projections-are-stably-vertex-induced: that straightens each algebraic projection to vertex-induced packets; this computes the simultaneous transition invariant for the smallest NAND cycle after that individual straightening.
---

In the three-dimensional standard `S_4` NAND packet, fix a shared separator
sign `S`.  Its plus space has the two atoms `e_(+,+),e_(+,-)` and its minus
space has the atom `e_(-,+)`.  Put

```text
D=C e_(+,+) directSum C e_(+,-) directSum C e_(-,+),
B={S}' intersect M_3(C)=M_2(C) directSum C.             (NKT1)
```

Here `D` is the full labelled context-atom algebra and `B` is the algebra of
all separator-preserving stable gauges.  Under determinant/Morita
coordinates, inclusion induces

```text
K_1^alg(D)=(C^x)^3  ->  K_1^alg(B)=(C^x)^2,
(a,b,c)             |-> (ab,c).                        (NKT2)
```

This map is surjective, so the determinant quotient vanishes:

```text
coker(K_1^alg(D) -> K_1^alg(B))=0.                     (NKT3)
```

This does **not** make the mapping-cone relative K-group vanish.  The
six-term sequence for `D -> B`, together with topological
`K_1(D)=K_1(B)=0`, gives

```text
K_1(B,D) isomorphic to ker(K_0(D) -> K_0(B)).           (NKT4)
```

Using minimal projections as generators, the `K_0` map is

```text
Z^3 -> Z^2,             (m,n,k) |-> (m+n,k),
K_1(B,D)=Z (1,-1,0).                                   (NKT5)
```

Thus there is one genuine relative index: the difference between the two
rank-one separator-plus atoms.  It is a finite-packet index, not a
nonmatricial one.

Let `H` be the plus-sheet swap, acting by the transposition matrix in the
`M_2` block and by `1` on the minus line.  Its algebraic determinant
coordinate is

```text
[H]=(-1,1)=(NKT2)(-1,1,1).                             (NKT6)
```

Thus atomwise diagonal gauge kills the determinant part of the swap.  The
relative transition triple `(e_(+,+),e_(+,-),H)` nevertheless has boundary
`[e_(+,+)]-[e_(+,-)]`, the generator in `(NKT5)`; this is the
orientation-sensitive plus-sheet exchange.  (The absolute unitary class of
`H` alone maps to zero in the relative group by `(NKT3)`.)  The central
phase `J=-I_3`, and hence the odd returned word `W_C=J`, has

```text
[J]=(1,-1)=(NKT2)(1,1,-1).                             (NKT7)
```

It lies in the atom gauge algebra itself and has zero relative boundary.  In
particular the odd **central phase** adds nothing to the atom-difference
index.  Stabilizing or replacing the individual carriers by the vertex-
induced packets of
`bass-serre-algebraic-projections-are-stably-vertex-induced` preserves only
copies of the same finite-rank difference.

The separator normalizer satisfies

```text
N_B(D)/U(D)=S_2.                                        (NKT8)
```

Its nontrivial element exchanges the two plus-atom generators of
`K_0(D)=Z^3` while fixing the minus atom.  Its oriented relative boundary is
the generator in `(NKT5)` (the reverse exchange gives its negative), while
forgetting orientation leaves the `S_2` bit.  This is exactly `h_C` from
`s4-nand-cycle-holonomy-is-one-s2-bit`.

For the minimal triangle this remaining datum has the exact model

```text
(C_2)^3 semidirect S_3 <= U(3),
W_C=J=-I_3,                                             (NKT9)
```

from `odd-nand-phase-return-has-exact-finite-models`.  Hence every consistent
2-cell which merely records the local identity `W_C J^(-1)=1`, or records
the odd Weyl bit and its phase lift, is realized in a finite group.  Adding
`W_C=1` while demanding `J=-1` is not a matrix-only obstruction: because
`W_C=J` is an algebraic consequence of the local relations, it makes the
desired commuting model inconsistent as well.

There is no general residual-finiteness theorem after arbitrary 2-cells are
allowed.  A graph of trivial finite groups is a free group, and arbitrary
finite 2-cell attachments give arbitrary finitely presented quotients.
Thus a further 2-cell can certainly destroy all relevant finite models, but
that effect is extra global group/BCS content; it is not supplied by the
minimal atom-difference index or central phase.  The simultaneous signed-
Hecke exception therefore narrows again: it must couple these finite-packet
indices through a genuinely global relative-position relation, beyond the
Weyl return of one predicate cycle.
