---
rg: 2
id: one-gram-vector-decodes-a-finite-bcs-strategy
kind: claim
title: One Gram vector decodes separate context occurrences into a finite BCS strategy
distinct_from:
  fixed-bcs-context-rounding-gives-commuting-strategy: that uses the tracial vector `1` and global normalized-HS closeness to the original tuple; this permits a nontracial state `vec(G)` and asks only for state-dependent occurrence consistency through one Gram operator.
  capacity-gated-common-corner-bcs-two-cell: that constructs a globally reducing projection and then applies the corner non-CE gap; this directly constructs the finite game strategy and never rounds a common projection.
  maximally-entangled-vectorization-is-hs-isometry: that treats the special maximally entangled vector `G=I`; this gives the exact weighted identity for an arbitrary Gram operator and includes forbidden-answer energy.
---

ESTABLISHED.
Let `B` be a finite constraint-variable BCS game.  For every context `c`, let

```text
(P_(c,a))_(a in {+1,-1}^(U_c))                         (OGV1)
```

be a PVM in `M_d(C)`, and put

```text
A_(c,x)=sum_a a_x P_(c,a),
F_c=sum_(a forbidden for c)P_(c,a).                    (OGV2)
```

Let `B_x` be a self-adjoint involution in `M_d(C)` for every variable.  Fix
one nonzero matrix `G in M_d(C)` and define

```text
N_G=||G||_2^2,

E_G
 =sum_(c,x) mu_(c,x)
    [||F_cG||_2^2+(1/4)||A_(c,x)G-GB_x||_2^2],         (OGV3)
```

where `mu` is the game's rational question distribution.  Then there is a
finite-dimensional tensor-product strategy `S_G` of local dimension `d`
such that

```text
1-value(S_G)<=E_G/N_G.                                 (OGV4)
```

Consequently, if the finite-dimensional value of the fixed game is at most
`theta<1`, every such matrix family obeys the Gram-Rayleigh gap

```text
E_G >=(1-theta)||G||_2^2.                              (OGV5)
```

## Proof

Let

```text
psi_G=vec(G)/||G||_2                                   (OGV6)
```

under the normalized vectorization convention.  Alice uses the PVM
`P_(c,a)` on the first tensor factor and Bob uses the entrywise conjugate of
the binary PVM of `B_x` on the second factor.  These are genuine commuting
finite-dimensional measurements.

For self-adjoint involutions `A=A_(c,x)` and `B=B_x`, vectorization gives

```text
<psi_G,(A tensor conjugate(B))psi_G>
 =tr(G^* A G B)/N_G.                                  (OGV7)
```

Since `A^2=B^2=I` and normalized trace is cyclic,

```text
||AG-GB||_2^2
 =2N_G-2 Re tr(G^* A G B).                            (OGV8)
```

The probability that Alice's `x`-bit disagrees with Bob is therefore

```text
Pr[a_x!=b | c,x]
 =||A_(c,x)G-GB_x||_2^2/(4N_G).                       (OGV9)
```

The probability that Alice returns a forbidden assignment is

```text
<psi_G,(F_c tensor I)psi_G>
 =tr(G^*F_cG)/N_G
 =||F_cG||_2^2/N_G.                                   (OGV10)
```

The losing event is contained in the union of forbidden answer and bit
disagreement.  Sum `(OGV9)--(OGV10)` with `mu` to obtain `(OGV4)`.  If
`omega^*(B)<=theta`, every finite-dimensional strategy has loss at least
`1-theta`; `(OGV4)` then implies `(OGV5)`.

The same proof works for any finite synchronous game after replacing
`(OGV3)` by the sum of its rejected answer-pair blocks.  The BCS form is
useful because the entire energy has the two explicit rows in `(OGV3)`.

## Fixed mixed moment list

For fixed packet PVMs and a fixed decoded Gram word/block `G`, every term in
`(OGV3)` is a fixed trace polynomial.  Explicitly,

```text
||F_cG||_2^2=tr(G^*F_cG),

||A_(c,x)G-GB_x||_2^2
 =2tr(G^*G)-2 Re tr(G^*A_(c,x)GB_x).                  (OGV11)
```

Thus the minimal state-dependent source interface is one norm moment
`tr(G^*G)` and the finite family

```text
tr(G^*F_cG),
tr(G^*A_(c,x)GB_x).                                   (OGV12)
```

No source projection, intersection of carriers, or polar rounding is
required.

## Bypass criterion for the static gap source

Let `G_cv` be the fixed finite game from
`oracularizable-tracial-nonru-game-exists`, and write

```text
omega^*(G_cv)<=theta<1.                                (OGV13)
```

Suppose a proposed group-word packet decoder produces, in every marked
finite matrix microstate, context PVMs, Bob involutions, and one fixed mixed
word block `G` satisfying

```text
||G||_2^2>=gamma q-o(1),
E_G<=K E_rel+o(1),                                    (OGV14)
```

where `q` is the marked/source mass and `gamma>0`.  Then `(OGV5)` gives

```text
K E_rel+o(1)>=(1-theta)gamma q.                        (OGV15)
```

This is already the required finite-dimensional payment.  It bypasses
`(NCL13)` and `(CSG4)`: the source need not be a common reducing projection;
one common state vector `vec(G)` is enough.

The construction remains matrix-only.  An exact non-CE tracial model gives a
perfect commuting strategy in its standard form, so the corresponding
infinite Gram vector may have zero game energy.  The finite lower bound
`(OGV5)` uses `omega^*<1` and does not extend to arbitrary finite von Neumann
algebras.  Hence this decoder passes the regular-representation firewall.

For the four native Fanizza contexts,
`fanizza-product-gram-reduces-to-one-state-holonomy` gives an explicit way to
manufacture the rows of `(OGV3)` from rooted context transports.  Three tree
edges and the attached leaf cost only their local covariance rows; the sole
additional gluing datum is the action of the triangle holonomy on the same
Gram operator.  The existing gauge/HNN bridges leave that multiplicity
holonomy arbitrary, so this is a reduction rather than a completed decoder.

`finite-game-gap-makes-the-cyclic-acceptance-compressor-strict` gives a
second exact packaging of `(OGV5)`.  The cyclic product of the finitely many
predicate and consistency **acceptance projections** is a strict contraction
on every finite Gram space.  Hence the entire list `(OGV12)` may be replaced
by one approximate return equation `T_game(G)≈G`; the open work becomes
constructing and authenticating that one finite Hecke bimodule return on a
positive-norm marked block.
