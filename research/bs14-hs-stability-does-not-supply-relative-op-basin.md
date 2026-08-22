---
rg: 2
id: bs14-hs-stability-does-not-supply-relative-op-basin
kind: claim
title: Known BS14 stability cannot supply the relative operator-norm basin
distinct_from:
  far-sector-is-solenoid-measure-rigidity: that proves HS stability of the amenable BS core through dense periodic measures; this audits why its topology is insufficient after cubic thresholding.
  bs14-cubic-rounding-leaves-relative-core-basin: that rounds the cubic spectral values and identifies the changed relative product; this computes the resulting approximate BS relation and audits the strongest available correction theorem.
  bs14-relative-involution-extension-stability: that asks for flexible normalized-HS repair of the full relative presentation; this is the narrower operator-norm-basin attempt.
---

Use the notation of `bs14-cubic-rounding-leaves-relative-core-basin`.  After
independently rounding `A=XS^2` and `B=XRS` to order-three unitaries
`Ahat,Bhat`, put

```text
Chat=Ahat^*Bhat.
```

The original `C=S^(-2)RS` itself satisfies

```text
C S C^*=S^4.                                          (ROB1)
```

Indeed, substitute `C=S^(-2)RS` and use `RSR^*=S^4`.
Consequently, if `eta` is the maximum operator-norm cubic defect, then

```text
||Chat S Chat^*-S^4||_op
 <=2||Chat-C||_op
 <=2 eta.                                             (ROB2)
```

Thus the alternating proposal reaches a completely explicit intermediate
object: `(Chat,S)` is an operator-norm approximate representation of
`BS(1,4)`.

The strongest established theorem represented in Cairn does **not** repair
`(ROB2)` in the topology needed by the mixed-norm Newton step.  The
Levit--Vigdorovich dense-periodic-measures theorem gives normalized-HS
stability of `BS(1,4)`.  Operator-norm matricial stability of `BS(1,4)` is
not supplied by that theorem.  The primary operator-norm literature leaves
this case open:

- Eilers--Shulman--Sorensen, *C*-stability of discrete groups*,
  arXiv:1808.06793v4, Section 4.4, proves the positive case `BS(1,-1)` and
  negative cases among other Baumslag--Solitar groups, not `BS(1,4)`;
- Dadarlat, *Obstructions to matricial stability of discrete groups and
  almost flat K-theory*, arXiv:2007.12655v2, Corollary 2.4 and the paragraph
  following it, states that matricial stability is unknown for the remaining
  Baumslag--Solitar groups, which include `BS(1,4)`.

Nor can HS correction be upgraded formally to the required operator-norm
coordinate tube.  Let `omega=exp(2 pi i/3)`.  For every `d`, the two exact
`BS(1,4)` cores

```text
(C_d,S_d)=(I_d,I_d),
(C'_d,S'_d)=(I_d, I_(d-1) direct_sum omega)
```

satisfy `(ROB1)`, because `omega^4=omega`, while

```text
||S_d-S'_d||_2=sqrt(3/d) ->0,
||S_d-S'_d||_op=sqrt(3).                              (ROB3)
```

So even inside the exact BS representation variety, normalized-HS
proximity gives no operator-norm tube.  Applying HS stability to `(ROB2)`
may change a small-rank spectral sector by operator norm `sqrt(3)` and hence
does not preserve the low-residual operator-norm hypothesis required by the
Newton estimate.

There is a second exact seam.  Even a hypothetical point-norm correction
`(Chat,S)->(C_0,S_0)` would not by itself preserve

```text
Bhat=Ahat Chat
```

or make `Ahat S_0^(-2)` the common involution which inverts the reconstructed
`R_0=S_0^2 C_0 S_0^(-1)`.  Alternating cubic and BS corrections therefore
needs a contraction or a joint relative lifting theorem; separate stability
of the two relation families does not imply stability of their union.

This audit neither proves nor refutes the relative operator-norm basin.  It
does prove that the proposed invocation of known BS stability is invalid,
and narrows a positive proof to one of the following genuinely new inputs:

1. a relative point-norm correction which preserves the common `X` and the
   product incidence, with a level-independent basin; or
2. a convergent alternating-projection estimate whose contraction constant
   is uniform over all periodic BS packets.

A Voiculescu clock--shift countersequence satisfying the exact BS and
dihedral relations while both cubic defects vanish in operator norm would
refute the basin, but no primary result above constructs such a relative
countersequence.
