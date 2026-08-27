---
rg: 2
id: partial-isometry-swap-wordizes-one-bcs-gram-row
kind: claim
title: A partial-isometry swap wordizes one BCS Gram row
distinct_from:
  controlled-swap-wordizes-matrix-corner-without-adjoint-dilution: that treats a commuting corner return `(R-I)Q`; this treats the general two-sided intertwining residual `AS-SB` and proves exact equivalence with one ordinary commutator word.
  one-gram-vector-decodes-a-finite-bcs-strategy: that proves a game gap for matrix residuals `F_cG` and `A_(c,x)G-GB_x`; this converts each such residual to a fixed group-word defect whenever the common Gram block is a partial isometry.
  paz-gram-vector-is-not-a-graph-projection: that rules out promoting one adjoint-space vector to a positive-density graph projection; this stays in a fixed `2d` matrix amplification and loses no factor depending on `d`.
---

ESTABLISHED.
Let `(M,tau)` be a finite tracial matrix algebra.  Let `S in M` be a
partial isometry and put

```text
P=SS^*,
Q=S^*S.                                                (PIS1)
```

For self-adjoint unitaries `A,B in M`, the matrix Gram row is

```text
R=AS-SB.                                               (PIS2)
```

There is one self-adjoint unitary, depending only on the partial isometry,
whose ordinary commutator with `diag(A,B)` is quantitatively equivalent to
`R`.

## The partial-isometry swap

In `M_2(M)` define

```text
J_S=[[I-P, S],
     [S^*, -(I-Q)]],

D_(A,B)=diag(A,B).                                     (PIS3)
```

The partial-isometry identities give

```text
J_S=J_S^*,
J_S^2=I.                                               (PIS4)
```

Indeed the diagonal entries of `J_S^2` are
`(I-P)^2+SS^*=I` and `S^*S+(I-Q)^2=I`, while the
off-diagonal entries vanish because `PS=S=SQ`.

Define the ordinary multiplicative commutator word

```text
C_(A,B;S)=D_(A,B) J_S D_(A,B) J_S.                    (PIS5)
```

Both factors in `(PIS5)` are involutions.

## Dimension-free equivalence

### Theorem

Exactly,

```text
||R||_2^2
 <=||C_(A,B;S)-I||_(2,tau_2)^2
 <=5||R||_2^2.                                        (PIS6)
```

In particular,

```text
C_(A,B;S)=I  iff  AS=SB.                              (PIS7)
```

The constants do not depend on the matrix dimension, the ranks of `P,Q`,
or the trace of the source.

### Proof

The additive commutator has block form

```text
[D_(A,B),J_S]
 =[[ [A,I-P],       R],
   [       -R^*, [B,Q]]].                             (PIS8)
```

Since multiplication by fixed unitaries preserves normalized
Hilbert--Schmidt norm,

```text
||C_(A,B;S)-I||_2=||[D_(A,B),J_S]||_2.                (PIS9)
```

The two off-diagonal blocks in `(PIS8)` already give

```text
||[D_(A,B),J_S]||_(2,tau_2)^2>=||R||_2^2.             (PIS10)
```

For the reverse estimate, use `(PIS2)` and its adjoint:

```text
A P-P A=R S^*-S R^*,
B Q-Q B=-R^*S+S^*R.                                   (PIS11)
```

Thus each diagonal block in `(PIS8)` has `2`-norm at most
`2||R||_2`.  Taking the normalized `2 by 2` block trace gives

```text
||[D_(A,B),J_S]||_2^2
 <=1/2(4+1+1+4)||R||_2^2
 =5||R||_2^2.                                         (PIS12)
```

This proves `(PIS6)`.  The lower bound proves the reverse implication in
`(PIS7)`; if `R=0`, `(PIS11)` makes the diagonal blocks vanish as well, so
the forward implication follows.  ∎

## BCS specialization

Let `G` be a projection serving as one common Gram block.  For a consistency
row take

```text
S=G,
A=A_(c,x),
B=B_x.                                                 (PIS13)
```

Then `(PIS6)` wordizes

```text
||A_(c,x)G-GB_x||_2^2                                 (PIS14)
```

by one commutator relator.  For a predicate rejection projection `F_c`,
take

```text
A=I-2F_c,
B=I,
S=G.                                                   (PIS15)
```

The row in `(PIS2)` is `-2F_cG`, so

```text
4||F_cG||_2^2
 <=||C_(I-2F_c,I;G)-I||_2^2
 <=20||F_cG||_2^2.                                    (PIS16)
```

Consequently, if one fixed packet supplies the same positive-norm
projection `G` and the reflection `J_G` in every context, the whole energy
from `one-gram-vector-decodes-a-finite-bcs-strategy` is bounded above and
below, up to constants depending only on the fixed game, by a finite sum of
ordinary group-word relator energies.  The finite game gap then pays
`||G||_2^2` with no cyclic compressor, graph projection on `L^2(M_d)`, or
adjoint-dimension loss.

The exact perfect model also passes the local firewall: every zero Gram row
in `(PIS14)` or `(PIS16)` makes its commutator relator exact by `(PIS7)`.

## What remains algebraic

The theorem does not manufacture `J_G`.  For a projection `G`, `(PIS3)` is
the copy swap controlled by the Boolean bit of `G`.  Its truth table is the
nonlinear rule `t=gk` identified in
`controlled-swap-wordizes-matrix-corner-without-adjoint-dilution`.
Commuting-involution/parity relations cannot force it.

Nor does the theorem align unrelated context carriers.  The same literal
`J_G` must occur in every row.  Giving context `c` a separate `J_(G_c)`
recreates the pairwise/direct-sum Gram escape.  Thus the remaining compiler
has been reduced to one finite static object:

```text
a common positive-mass nonlinear controlled swap J_G,
plus the ordinary block involutions D_(A_(c,x),B_x)
and D_(I-2F_c,I).                                      (PIS17)
```

Once `(PIS17)` is authenticated on one marked finite-matrix carrier, the
dimension-free soundness calculation is complete by `(PIS6)` and the fixed
game gap.

## Attempts

- **Use the PAZ Gram vector directly.**  `J_S` requires a matrix partial
  isometry, not a rank-one projection in `End(L^2(M_d))`; the latter loses
  `d^(-2)`.
- **Give every context its own switch.**  This supplies only separate Gram
  states and is defeated by the exact pairwise/direct-sum countermodels.
- **Build the switch from commuting involutions.**  The control truth table
  is nonlinear, so affine parity relations cannot name it.
- **Replace `J_G` by a global full swap.**  This corresponds to `G=I` and
  forces full operator equality between the two occurrences; it is useful
  only if exact infinite completeness supplies a full left--right module
  intertwiner, which is a stronger source-saturation condition than one
  perfect Gram vector.
