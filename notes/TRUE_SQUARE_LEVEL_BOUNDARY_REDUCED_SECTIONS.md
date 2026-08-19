# Boundary-reduced square-level packets and an exact primal section at level 121

Date: 2026-08-12

## 1. Outcome

The exact cellular packets from
`TRUE_SQUARE_LEVEL_EXACT_CYCLE_PACKETS.md` can be shortened substantially by
adding literal integral rows of `d_3`.  The best full spanning packets found
in the combined natural/reverse circuit families are:

| level | `dim_Q H_2` | maximum support | maximum squared norm | maximum coefficient | maximum Gram row sum |
|---:|---:|---:|---:|---:|---:|
| `121` | `7` | `95` | `95` | `2` | `122` |
| `169` | `12` | `133` | `133` | `2` | `211` |

The previous corresponding bounds were respectively

```text
level 121: support 311, norm^2 871, coefficient 4, row sum 1119;
level 169: support 220, norm^2 942, coefficient 7, row sum 1658.       (BRS1)
```

At level `169`, eleven of the twelve selected cycles have coefficients only
`0,+-1`; the four natural-order classes have squared norms

```text
5,32,36,50,                                                       (BRS2)
```

and the eight selected reverse-order classes have squared norms

```text
63,87,97,108,114,124,125,133.                                    (BRS3)
```

At level `121`, the two natural-order classes have squared norms `35,40`,
and the five selected reverse-order classes have squared norms

```text
46,78,85,89,95.                                                   (BRS4)
```

These are exact integral cycles and their quotient signatures have full
rank.  The reduction is an upper-bound certificate: it uses an independent
set of actual boundary rows, LLL, and Babai nearest plane.  It is neither a
CVP optimum nor a lower bound, and the chosen boundary rows need not generate
the saturated integral boundary lattice.

The stronger level-`121` result is integral, not merely rational:

```text
the projections of the seven selected cycles form a Z-basis of Q_121.       (BRS5)
```

Thus the projection sequence from integral cellular cycles onto the primal
harmonic lattice splits integrally in this chart.  Transporting the already
certified short LLL basis of `Q_121` through this splitting and reducing the
seven lifts again by boundaries gives representatives with coefficients only
`0,+-1` and squared norms

```text
46,78,78,125,130,154,198.                                        (BRS6)
```

The exact generalized section polynomial is stored in the certificate.  Its
largest root is

```text
204.98708809920473448...,
```

so the resulting primal projection section has operator norm

```text
14.31737015304154014....                                         (BRS7)
```

This closes integral saturation and bounded absolute realization for all
seven new level-`121` primal harmonic directions.  It does **not** construct
the different dual carry section

```text
0 -> L -> M_Sigma -> Q^# -> 0                                    (BRS8)
```

from `TRUE_HARMONIC_INTEGRAL_LIFT_SEQUENCE.md`.  Hence `(BRS7)` is not by
itself a circle-repair theorem.

## 2. The exact index test

Let `K` be an integral cycle lattice in a Euclidean space, let `H` be a
rational harmonic subspace, and put

```text
Q=P_H(K).                                                         (BRS9)
```

Choose a basis `u_1,...,u_r` of `Q^#` and integral cycles
`c_1,...,c_r in K`.  Define

```text
M_(j,i)=<u_j,c_i>=<u_j,P_H c_i>.                                 (BRS10)
```

**Proposition 1 (pairing determinant).**  If `det M!=0`, then

```text
[Q : sum_i Z P_H(c_i)]=|det M|.                                  (BRS11)
```

In particular, `det M=+-1` if and only if the projected cycles are a
`Z`-basis of `Q`.

**Proof.**  The basis of `Q` algebraically dual to `u_1,...,u_r` identifies
`Q` with `Z^r`.  In these coordinates the columns of `M` are exactly the
vectors `P_H(c_i)`.  The index of their column lattice is `|det M|`.  End
proof.

If `det M=+-1`, sending `P_H(c_i)` back to `c_i` defines a `Z`-linear
section of `P_H:K->Q`.  Let

```text
G_K=(<c_i,c_j>),       G_Q=(<P_Hc_i,P_Hc_j>).                      (BRS12)
```

Its squared operator norm is the largest generalized eigenvalue of

```text
G_K v=lambda G_Q v,                                               (BRS13)
```

equivalently the largest real root of `det(G_K-t G_Q)` after monic
normalization.  This makes both `(BRS11)` and the section norm exactly
certifiable with rational arithmetic.

## 3. Level-121 determinant-one certificate

The harmonic exporter gives an integral matrix `H` spanning the rational
harmonic space.  If `B` is a basis of the lattice of all pairings of the
rows of `H` with integral cycles, then

```text
(B^T)^(-1) H                                                       (BRS14)
```

is a basis of `Q^#`.  Pairing `(BRS14)` with the seven boundary-reduced
cycles gives an integral `7 x 7` matrix of determinant `+-1`.  Proposition
1 proves `(BRS5)` without assuming that the harmonic basis itself is
primitive.

The initial determinant-one packet has ambient squared-norm maximum `95`
and section norm

```text
24.73710252023889183....                                          (BRS15)
```

The unimodular basis change from
`projective-cellular-n121-primal-packet.json` is then transported through
the exact packet.  After boundary reduction, its ambient Gram matrix is

```text
[[ 46,  0,  0, -1,  3, -2, -6],
 [  0, 78,  7, -5,  2, -7, -3],
 [  0,  7, 78,  4,  1,  2,  2],
 [ -1, -5,  4,125,  4, -4, -1],
 [  3,  2,  1,  4,130,  1,  0],
 [ -2, -7,  2, -4,  1,154, -5],
 [ -6, -3,  2, -1,  0, -5,198]].                                (BRS16)
```

Its maximum absolute row sum is `215`.  Recomputing `(BRS10)--(BRS13)`
verifies determinant one again and gives `(BRS7)`.

## 4. A tempting but invalid identification

The ambient Gram matrices of the selected packets split exactly into blocks
of sizes

```text
2+5 at level 121,       4+8 at level 169.                         (BRS17)
```

These dimensions match the cuspidal/Eisenstein dimensions.  This does not
identify the blocks.  Exact testing shows that none of the natural-order
cycles is itself harmonic: their pairings with `d_3` are nonzero.  At level
`121`, the harmonic projections of the two ambient blocks also have nonzero
cross pairings.  Thus the block diagonal ambient Gram matrix is a property
of the chosen boundary representatives, not a canonical cuspidal--
Eisenstein orthogonal decomposition.  The absolute-to-relative comparison
map remains necessary.

## 5. What this changes for TRUE

The finite evidence now rules out three weaker diagnoses at the tested
square levels:

1. rational homology directions do not require large coefficients;
2. adding actual boundaries removes the previously largest supports and
   norms; and
3. at level `121`, the packet is not hidden in a high-index sublattice of
   `Q`: its pairing determinant is exactly one.

The family-level theorem-shaped target is therefore precise:

> construct, at every projective square level, a full packet of integral
> cycles whose projected pairing determinant is one and whose primal section
> norm in `(BRS13)` is uniformly bounded.

This would give a uniform integral realization of the primal harmonic
lattice and, by the bounded-spanning theorem, uniform denominator control.
The dual extension `(BRS8)` would still need its own uniformly bounded
section to finish nonlinear circle repair.

## 6. Certificates

```text
experiments/projective-cellular-n121-cycle-boundary-combined.json
SHA-256 2965d5bc9a79721b55b527fb51128bb88efa42f2b0e5ddd600acdce601f664d6

experiments/projective-cellular-n169-cycle-boundary-combined.json
SHA-256 148cbe60a18a27ccf937d4a5d28b5b9713e3cc8b2cbe1afc657b16c16db49088

experiments/projective-cellular-n121-cycle-packet-section.json
SHA-256 87a05ae92d1cc86012df66940fc84d030fd81df580e3cdbdd9ff8061fc56bea4

experiments/projective-cellular-n121-primal-cycle-packet.json
SHA-256 bb39c17be6290e3dd6de404e80ee8eb0ba829508e1ca73877a2dbe532ca3f96d

experiments/projective-cellular-n121-primal-cycle-boundary-reduced.json
SHA-256 cd42f5009796471f28016c39fc3715361f3ba3ce2538b26717ddb7e03cd9ffe3

experiments/projective-cellular-n121-primal-cycle-section.json
SHA-256 06b93b9ac1e0816b34c334eec562bf63d0d2cbd540876ad4cbe1c944d5d0f7a5
```

The natural-packet harmonic tests are recorded separately to prevent the
false inference discussed in Section 4.
