---
rg: 2
id: opnorm-common-intertwiner-pi-gap-is-sparse-terminal
kind: claim
title: One common operator-norm PI intertwiner is terminal on any nonzero corner
artifacts:
  - research/opnorm-common-intertwiner-pi-gap-proof.md
distinct_from:
  fixed-pi-degree-fingerprints-packet-label-factor: that needs a positive normalized-trace carrier because its endpoint is Hilbert--Schmidt nonhyperlinearity; this is the operator-MF endpoint and works on an arbitrarily sparse nonzero matrix corner.
  one-common-intertwiner-carries-the-four-pauli-pi-bridge: that asks the group-word package to produce the common intertwiner; this proves the terminal operator-norm contradiction after it has been authenticated.
  positive-toeplitz-head-is-square-defect-or-rectangular-escape: that uses direct finiteness of one square Toeplitz pair; this uses a fixed polynomial identity to distinguish a source label algebra from a transverse target algebra, without measuring spectator multiplicity.
---

**ESTABLISHED.**  Fix `m>=1` and the degree-`m` standard polynomial

```text
s_m(Z_1,...,Z_m)=sum_(sigma in Sym(m))
                   sign(sigma) Z_(sigma(1))...Z_(sigma(m)).       (SPI1)
```

Let `P` be a nonzero matrix projection.  Suppose `C_1,...,C_m` and
`D_1,...,D_m` are contractions in `P M_d(C) P`, and `T` is a contraction in
the same corner.  Put

```text
eta=||TT^*-P||_op,
delta=sum_j ||D_j T-T C_j||_op.                         (SPI2)
```

If

```text
s_m(C_1,...,C_m)=0,
||s_m(D_1,...,D_m)||_op>=kappa>0,                       (SPI3)
```

then

```text
(1-eta) kappa <= m! delta.                              (SPI4)
```

Consequently there is no sequence of such data, in arbitrary matrix sizes
and on arbitrary nonzero projections, with fixed `kappa>0` and
`eta,delta->0`.

For the fixed-degree PI program take `m=2r`.  A source tuple contained in a
copy of `M_r tensor I` has `s_(2r)(C)=0` by Amitsur--Levitzki, while a fixed
tuple generating the transverse `M_(r^2)` label factor can be chosen with
operator-norm PI value `kappa_r>0`.  Formula `(SPI4)` is unchanged by an
arbitrary common tensor spectator and does not involve `rank(P)/d`.

Thus an operator-MF attack on the Jacobson head does **not** need the
positive-density clause in `fixed-pi-degree-fingerprints-packet-label-factor`.
The rounded nonzero spectral cut of the surviving involution is enough.  The
whole remaining debt is semantic: the group relations must authenticate the
same contraction `T` in all `2r` intertwining rows on that selected corner.
Separate branch transports, an abstract isomorphism of packet types, or an
untyped analytic selector do not meet this hypothesis.

DERIVATION
opnorm-common-intertwiner-pi-gap-proof
