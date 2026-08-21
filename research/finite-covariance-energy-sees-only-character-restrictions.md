---
rg: 2
id: finite-covariance-energy-sees-only-character-restrictions
kind: claim
title: Finite lamp covariance energy sees only a finite character-restriction quotient
distinct_from:
  infinite-character-actor-word-energy-interface: that asks for a finite-presentation mechanism controlling the full infinite-orbit transport energy; this identifies the exact kernel of the direct finite-covariance calculation and the additional mechanism such an interface must supply.
  word-recursion-cannot-amplify-sublinear-summands: that is a direct-sum density obstruction; this is a spectral-resolution obstruction even on a carrier of full normalized trace.
  finite-normalizer-star-no-go: that uses a finite packet's regular representation; this is an exact block-energy identity for an arbitrary elementary-abelian spectral PVM.
---

ESTABLISHED.  Let `M` be an elementary abelian two-group, let `s` act on
`M`, and let

```text
rho(m)=sum_(chi in Omega) chi(m) P_chi
```

be an exact finite-support spectral representation on a finite-dimensional
tracial Hilbert space.  Write `(s chi)(m)=chi(s^(-1)m)`, let `C` be a
unitary, and put

```text
E_s=sum_chi ||C P_chi C^*-P_(s chi)||_2^2,
d_m=||C rho(m) C^*-rho(s m)||_2.                         (FCR1)
```

For a finite set `T subset M`, define

```text
h_T(psi,s chi)=|{m in T : chi(m)!=psi(s m)}|.
```

Then the exact block identities are

```text
E_s=2 sum_(psi!=s chi) ||P_psi C P_chi||_2^2,             (FCR2)
sum_(m in T) d_m^2
   =4 sum_(chi,psi) h_T(psi,s chi)||P_psi C P_chi||_2^2.  (FCR3)
```

Consequently finite covariance tests control precisely transport between
different restriction labels and are blind inside each fiber of

```text
Omega -> {+1,-1}^(sT),       psi |-> psi|_(sT).            (FCR4)
```

If `(FCR4)` is injective, one gets the sharp dimension-free comparison

```text
(1/(2|T|)) sum_(m in T)d_m^2 <= E_s
                                  <= (1/2)sum_(m in T)d_m^2. (FCR5)
```

Conversely, if `psi!=psi'` agree on `sT`, put
`chi=s^(-1)psi'`.  The off-diagonal block from `P_chi` to `P_psi` contributes
positively to `(FCR2)` but zero to every summand in `(FCR3)`.  Thus no
positive **termwise** coercivity constant can hold between these two block
quadratic forms.

There is also an honest-unitary counterexample to fine spectral recovery,
not merely a bad formal block.  Take `s=1`, put equal-rank spectral
projections on two distinct characters with the same `T`-restriction, and
let `C` swap them.  Then every `d_m`, `m in T`, is zero, whereas `E_1=2`.

In particular, when `Omega` is infinite, every finite `T` has a collision by
the pigeonhole principle.  Adding any finite depth of conjugated covariance
checks merely replaces `T` by another finite set and leaves an infinite
invisible fiber.  Therefore an infinite Schreier gap cannot by itself turn
finitely many lamp covariance defects into the fine-character transport
energy `(ISC2)`.  A successful finite-presentation interface must additionally
do one of the following:

1. collapse the occurring spectral support injectively onto finitely many
   restriction labels;
2. encode an infinite-resolution square function in one fixed operator
   defect; or
3. use a matrix-only rigidity statement which forbids transport inside the
   restriction fibers.

The obstruction is not trace dilution: the PVM may fill the whole carrier.
It is loss of spectral resolution, so ordinary nonamenable replication or
finite word recursion does not repair it.

The finite-exponent hypothesis only makes the failure exact.  For an
arbitrary abelian `M`, the finite restriction map lands in the compact torus
`T^T`.  Every infinite `Omega` contains distinct characters with arbitrarily
close restrictions.  The same two-character swap has `E_1=2` while

```text
sum_(m in T)||[C,rho(m)]||_2^2
   =sum_(m in T)|chi(m)-psi(m)|^2 -> 0.                  (FCR6)
```

Thus replacing binary lamps by infinite-order abelian lamps cannot restore a
dimension-free finite-test resolution constant: exact collisions become
arbitrarily close collisions by compactness.
