---
rg: 2
id: bs14-long-packet-monodromy-reset-creates-fixed-sources
kind: claim
title: Long BS14 packet monodromy resets to one at inverse-orbit HS cost
distinct_from:
  bs14-trivial-boundary-inversion-forces-r-fixed-source: that says a source requires monodromy eigenvalue one; this gives an explicit exact-BS type change which creates those sources.
  bs14-full-commutant-finite-period-preconditioner: that rounds the whole BS pair to bounded periods; this changes only return monodromy and has an exact inverse-orbit cost.
  bs14-native-cell-padding-preserves-lattice-charge: that fences same-support padding; this is a genuine support-enlarging type change.
---

Consider one length-`m`, multiplicity-`k` BS packet in the gauge `(BP3)`--
`(BP4)`.  Thus all non-return edge maps of `R` are the identity and the
return map is `V in U(k)`.  Choose the principal logarithm

```text
V=exp(iH),                 spec(H) subset [-pi,pi],
W=exp(-iH/m).                                      (LMR1)
```

Multiply every one of the `m` cyclic edge maps of `R` on the right by `W`
(on the return edge use `VW`).  The resulting weighted cyclic shift `R_0`
still satisfies

```text
R_0 S R_0^(-1)=S^4,          R_0^m=1.               (LMR2)
```

Indeed all edge maps commute with the scalar action of `S` on their orbit
spaces, and their cyclic product is `V W^m=1`.  Moreover

```text
||R-R_0||_F^2
 =m ||1-W||_F^2
 =4m sum_(ell=1)^k sin^2(theta_ell/(2m))
 <= (1/m) sum_ell theta_ell^2
 <= pi^2 k/m,                                        (LMR3)
```

where `exp(i theta_ell)` are the eigenvalues of `V`.  Relative to the packet
dimension `mk`,

```text
||R-R_0||_(2,mk) <= pi/m.                            (LMR4)
```

The new fixed space has dimension `k`, namely the orbit-sum copy of the
whole multiplicity space.  More selectively, diagonalizing `V` and applying
the construction on chosen scalar eigensummands resets precisely those
return phases and creates one `R_0`-fixed source per selected scalar packet.

Consequently all packets of length at least `M` in an arbitrary exact BS
core can have their monodromies reset simultaneously, without changing
`S`, at global normalized-HS cost at most `pi/M`.  This is a concrete
support-enlarging operation for the `v!=1` sector; no invariant hull is
taken and the BS relation remains exact throughout.

This does not yet close active dilation.  Changing `R` also perturbs the
inversion and second cubic relators involving `X`, and a final exact `X`
must still be rebuilt.  Short packets have no small orbit-length factor:
their exact cost is the left side of `(LMR3)`, which can be a fixed fraction
of their rank.  Such short active mass can be energy-paid only after proving
that the residual polar data localize to the scalar packet summands; a high
singular subspace may otherwise be spread thinly across many packets.

Finally, the mod-two charge in
`bs14-native-cell-padding-preserves-lattice-charge` is an abstract support
counterexample, not a charge already computed for the native BS/Iwahori
cell set.  Its bit labels were freely chosen in `(TET4)`.  Therefore there
is presently no rigorous "minimal native odd cell" to identify.  The next
finite algebraic task is to compute the actual support of joint cells after
the monodromy-one reset and then its incidence lattice; importing the
abstract parity labels as native packet invariants would be circular.

