---
rg: 2
id: agent-aggregate-escape-rfd-support-orientation-firewall
kind: claim
title: A support-orientation two-cell must put every forbidden marked corner in the finite-dimensional radical
distinct_from:
  agent-aggregate-escape-central-support-orientation-terminal: that proves one aggregate support estimate is sufficient for nonhyperlinearity; this gives an exact representation-theoretic obstruction to obtaining that estimate from RFD, Bass--Serre, triangle-face, or spectator-covariance cells.
  canonical-types-extend-every-finite-bass-serre-actor: that extends canonical ultraproduct types through finite Bass--Serre actors; this already refutes the support estimate using one exact finite-dimensional representation whenever the relevant finite marked packet embeds.
  packet-kazhdan-commutant-placement-decouples: that gives a tensor countermodel for one Kazhdan compressor proposal; this isolates the general extension property which makes any actor or independent correction fail.
---

**ESTABLISHED RFD FIREWALL.**  Keep the role-packed forbidden summands

```text
e_i=R_iP_i,                 B_f=sum_i e_i,
T=(1-K)/2,
```

where `K` is the proposed central orientation sign.  Let `Gamma` be any
ordinary group extension of the structural and role packet presentation.
If the exact (`E=0`) case of `(ACO4)` holds in every finite-dimensional
unitary representation of `Gamma`, then

```text
pi(T e_i)=0                                             (RF1)
```

for every forbidden type `i` and every finite-dimensional `pi`.  Thus every
marked forbidden corner `T e_i` belongs to the finite-dimensional radical

```text
Rad_fd(C*(Gamma))=intersection_(pi finite-dimensional) ker(pi). (RF2)
```

In particular, if one `T e_i` is nonzero in `C*(Gamma)`, then `C*(Gamma)` is
not residually finite-dimensional.  If `Gamma` is residually finite, the
same conclusion follows already in the complex group algebra: finite
quotients separate the finite support of `T e_i`, and their regular
representations detect it.  Consequently no residually finite extension
which preserves one marked local packet can satisfy `(ACO4)`.

There is a useful local criterion for nonvanishing.  Let `F_i` be the finite
central product of the context packet and role packet on which `e_i` is its
nonzero character idempotent.  If

```text
<F_i,K> = F_i direct_product <K>                       (RF3)
```

embeds in `Gamma`, then `T e_i` is a nonzero idempotent of
`C[<F_i,K>]`, hence is nonzero in `C*(Gamma)`.  Therefore `(ACO4)` forces a
genuinely non-RFD cross-context relation: either `(RF3)` must cease to embed,
or a nonzero local corner must be placed in the finite-dimensional radical.
Merely adding more finite packet covariance does neither.

The countermodel has fixed density, not merely nonzero rank.  In any finite
quotient which is injective on `<F_i,K>`, its normalized regular trace
restricts to the normalized regular trace of that subgroup, and hence

```text
tau(T e_i)=1/2 tau_(F_i)(e_i)>0.                        (RF3')
```

For the literal role/context character idempotent of a `k_i`-variable
context this is `1/(2 m 2^(k_i+1))` with the conventions of `(RFW1)`.
Amplifying the quotient does not dilute this number.

## Three candidate mechanisms

1. **Proper-corner Reynolds/Schur cell.**  Before global first-hit placement,
   the balanced Schur packet and companion-sign packet form a finite base,
   and the Reynolds section is an HNN edge between finite subgroups.  The
   base embeds by Britton's lemma and the resulting finite graph-of-finite-
   groups cell is virtually free, hence residually finite.  Its finite
   quotients therefore give exact matrix representations with
   `T e_i!=0` and zero presentation defect.  The cell supplies an exit of
   equal forbidden mass; it cannot by itself turn that mass into `(ACO4)`.

2. **Nonamenable or Kazhdan actor attached only by commutant/covariance
   rows.**  If the marked packet representation extends by spectator tensor
   amplification, `(RF1)` fails immediately.  The exact sign-twist models of
   `kazhdan-and-transverse-packets-cannot-orient-clifford-twist` and the
   tensor model of `packet-kazhdan-commutant-placement-decouples` provide
   precisely such extensions.  Property `(T)` controls off-commutant motion
   but cannot choose a point in the amplified multiplicity algebra.

3. **Triangle finite-face cp balancing.**  The explicit finite-face section
   and its `2/L^2` two-edge obstruction concern operator-norm displacement of
   ucp lifts; they impose no group relation placing `T e_i` in `(RF2)`.
   Moreover the obstruction has an exact direct-sum dilution: one
   finite-dimensional representation of the virtually free edge group
   detects it, while arbitrarily many representations factoring through the
   finite face see zero lift discrepancy.  The operator norm stays bounded
   below and the normalized-HS density tends to zero.
   Hence it cannot imply `(ACO4)` without an additional positive-density
   coupling of the triangle holonomy to the forbidden corner.  Such a
   groupification would have to destroy the RFD countermodel and is exactly
   a new support-orientation two-cell, not a consequence of one-face or
   simultaneous cp balancing alone.

## Sharp surviving design condition

Call an attachment **marked-extension-functorial** if every exact
finite-dimensional representation of the local packet with `T e_i!=0`
extends, after finite amplification, to the attachment.  Every such
attachment fails `(ACO4)` at `E=0`.  Therefore a successful two-cell must
exclude all marked extensions and do so quantitatively:

```text
||pi(T e_i)||_2^2 <= C sqrt(E(pi)).                    (RF4)
```

This is stronger than nonamenability, non-RFD, a ucp lifting obstruction, or
a proper-corner rank identity.  It is an explicit **HS-radical modulus** for
the finite list of group-algebra corners `T e_i`.  Constructing that modulus
while the perfect tracial BCS representation survives is exactly the
remaining cross-context gate.

DERIVATION
agent-aggregate-escape-rfd-support-orientation-firewall via agent-aggregate-escape-rfd-support-orientation-proof
