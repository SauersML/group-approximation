---
rg: 2
id: canonical-marked-reynolds-return-is-subgroup-intersection
kind: claim
title: A canonical marked Reynolds return is exactly a quotient-subgroup intersection density
distinct_from:
  balanced-controlled-whitehead-return-checksum: that gives the finite trace-square checksum and a representation-theoretic rank upper bound; this evaluates the checksum exactly in the canonical marked trace for every actuator word.
  finite-edge-reynolds-overlap-follows-character-transport: that transports character-resolved Reynolds ranges through an HNN edge; this needs no edge relation and computes an arbitrary mixed return from subgroup intersection.
---

**ESTABLISHED.**  Let `Gamma` contain a nontrivial central involution `J`,
and let `A,B<=Gamma` be finite subgroups containing `J`.  Put

```text
q=(1-J)/2,
Abar=A/<J>,                 Bbar=B/<J>.                (CMR1)
```

On the canonical marked corner `q L(Gamma)`, let `R_A,R_B` be the adjoint
Reynolds projections and let `w in Gamma`.  With normalized trace on the
marked corner and on its Hilbert--Schmidt operator space, set

```text
Theta_w=tr_ad(R_A Ad(w)^* R_B Ad(w) R_A).              (CMR2)
```

Then

```text
Theta_w
 = |Abar intersect w^(-1) Bbar w|/(|Abar||Bbar|).      (CMR3)
```

Here the intersection is taken in `Gamma/<J>`.  In particular

```text
Theta_w<=min(1/|Abar|,1/|Bbar|),                       (CMR4)
```

and full return to the `A`-Reynolds range,

```text
Theta_w=tr_ad(R_A)=1/|Abar|,                           (CMR5)
```

holds exactly when

```text
w^(-1) Bbar w <= Abar.                                (CMR6)
```

Thus an exact mixed return is a reverse subgroup inclusion, not an
orientation-selection phenomenon.

For the two-qubit Pauli packet `P` and its controlled-reflection extension
`G`, one has

```text
|Pbar|=16,                  |Gbar|=32.                 (CMR7)
```

Consequently every group word `w`, normalizing or not, satisfies

```text
Theta_w<=1/32,
tr_ad(R_P)-Theta_w>=1/32.                              (CMR8)
```

The desired `1/16` return in `(BCW6)` therefore cannot be a consequence of
exact ordinary group relations or of a zero-defect algebraic Whitehead
identity.  Such a consequence would hold in the canonical regular
representation, contradicting `(CMR8)`.  A successful return estimate must
be genuinely finite-matrix-only (for example a finite trace or multiplicity
inequality which is false in the infinite regular representation).

This removes both orientation and normality as possible loopholes in the
exact one-row approach.  Breaking the `C_2` orientation grading is necessary
to eliminate the balanced finite-packet double, but it is not sufficient:
even a completely nonnormal actuator has the canonical intersection ceiling
`(CMR8)`.

The same formula gives a sharp selector warning.  An *unconditioned*
Reynolds return sees only `Abar`, `Bbar`, and their conjugate intersection;
it cannot measure a local Fano ghost projection.  Conditioning the return on
a selector character introduces a physical character carrier and returns to
the induced-sector/affine-support firewalls in
`ghost-finite-router-induced-sector-or-perfect-corner` and
`range-local-finite-edge-authentication-is-affine`.  Hence one fixed finite
edge has only two outcomes: a selector-blind intersection checksum, or an
affine character-conditioned range.  Neither is the nonlinear Fano payment.

