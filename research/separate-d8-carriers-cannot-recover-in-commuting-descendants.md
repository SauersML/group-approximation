---
rg: 2
id: separate-d8-carriers-cannot-recover-in-commuting-descendants
kind: claim
title: Two D8-holonomy carriers cannot separately recover inside commuting descendant algebras
distinct_from:
  tensor-independent-child-carrier-gap: that puts one projection near both trace-independent algebras; this puts the two distinct canonical quarter carriers near two merely commuting algebras and uses their fixed D8 holonomy.
  balanced-router-pauli-holonomy-interface: that exposes the two projection reflections as ordinary derived-packet words; this needs only algebra membership of the projections after fixed-packet decoding.
---

Let `F,G` be projections in a finite tracial von Neumann algebra and write

```text
R_F=2F-1,       R_G=2G-1,
h(F,G)=||R_F R_G R_F R_G-1||_2.                       (SDR1)
```

Let `A,B` be commuting von Neumann subalgebras.  Then

```text
h(F,G)
 <= 4 sqrt(2) (dist_2(F,A)+dist_2(G,B)).              (SDR2)
```

More generally, if `P in A` and `Q in B` are the rounded projections below
and their reflection holonomy is at most `eta`, then

```text
h(F,G)
 <= eta+4 sqrt(2) (dist_2(F,A)+dist_2(G,B)).          (SDR3)
```

For the two exact atlas quarter carriers,

```text
h(F,G)^2=1/2.
```

Consequently any recovery into commuting descendants satisfies the fixed
dimension-free floor

```text
dist_2(F,A)+dist_2(G,B) >= 1/8.                        (SDR4)
```

## Proof

Put `a=E_A(F)`, where `E_A` is the trace-preserving conditional
expectation.  Since `F` is a projection and `E_A` is the orthogonal
projection in `L^2`,

```text
tau(a-a^2)=||F-a||_2^2.                               (SDR5)
```

Let `P=1_[1/2,1](a)`.  Pointwise on `[0,1]`,

```text
|1_[1/2,1](t)-t|^2 <= t(1-t),
```

so

```text
||a-P||_2 <= ||F-a||_2,
||F-P||_2 <= sqrt(2) dist_2(F,A).                     (SDR6)
```

The second estimate uses Pythagoras: `F-a` is orthogonal to `A`, while
`a-P` belongs to `A`.

Apply the same construction to `G` and `B`, obtaining a projection `Q` with

```text
||G-Q||_2 <= sqrt(2) dist_2(G,B).                     (SDR7)
```

Because `A` and `B` commute, `P` and `Q` commute, and hence their projection
reflections have trivial group commutator.  Telescoping the four-letter
reflection word, using unitary invariance of normalized Hilbert--Schmidt
norm, gives

```text
h(F,G)
 <= 2||R_F-R_P||_2+2||R_G-R_Q||_2
 = 4||F-P||_2+4||G-Q||_2,
```

which is `(SDR2)`.  Keeping the returned reflection holonomy as an error term
gives `(SDR3)`.

## Consequence for the affine/Pauli atlas

The mixed return no longer has to recover one common projection inside both
transverse descendants.  It is sufficient to recover the already canonical
common transported corner `F` in one descendant and the already canonical
branch-transfer carrier `G` in the other, while the rank-five relations make
the two descendant algebras commute (after their fixed finite tables have
been exactified).  The canonical trace moments force `h(F,G)^2=1/2`, whereas
the returned descendants force `h(F,G)=o(1)` by `(SDR2)`.

This endpoint uses the projections as fixed group-algebra/Hecke expressions;
their reflections need not first be exposed as ordinary group words.  The
remaining placement theorem is therefore separate native-carrier recovery,
which is strictly weaker than both ordinary-word router exposure and
same-carrier transverse recovery.
