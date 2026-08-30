---
rg: 2
id: weyl-return-frame-is-exact-rectangular-escape
kind: claim
title: The full Weyl return frame is exactly the multilevel rectangular escape
distinct_from:
  leavitt-target-return-channel-count-firewall: that proves the abstract sharp channel count from ranks; this constructs the canonical Weyl-indexed sharp frame on every Heisenberg refinement and shows that packet-symmetric aggregation realizes, rather than detects, rectangular escape.
  heisenberg-self-copy-relators-do-not-pay-reservoir-loss: that compares source and target commutant densities in one self-copy window; this decomposes the whole source commutant into target-sized return channels and computes every channel Gram.
  finite-tags-do-not-atomize-heisenberg-schrodinger-tower: that proves decay of polarized representation-space atoms; this proves an exact Parseval decomposition on the adjoint multiplicity space after aggregating all exponentially many atoms.
---

**ESTABLISHED ALL-DEPTH FRAME OBSTRUCTION.**  Let `p` be prime, let the
source Heisenberg label have dimension `p^L`, and refine it by `r>=1`
coordinates.  On

```text
K=C^(p^L) tensor C^(p^r) tensor C^m
```

write `R_s,R_t` for the adjoint Reynolds projections of the source and
refined packets.  Thus

```text
Ran(R_s)=I_(p^L) tensor M_(p^r) tensor M_m,
Ran(R_t)=I_(p^(L+r)) tensor M_m,                         (WRF1)
tr_ad(R_s)=p^(-2L),
tr_ad(R_t)=p^(-2(L+r)).                                 (WRF2)
```

Let `{W_a:a in F_p^(2r)}` be the standard Weyl unitary error basis of
`M_(p^r)`, orthonormal for normalized trace.  On the normalized
Hilbert--Schmidt space `M_(dim K)`, let `L_a` denote left multiplication by
`I tensor W_a^* tensor I`, and put

```text
X_a=R_t L_a R_s.                                       (WRF3)
```

Then every `X_a` is a partial isometry from a target-sized orthogonal
summand of `Ran(R_s)` onto all of `Ran(R_t)`.  More precisely, there are
orthogonal projections `P_a` such that

```text
X_a^*X_a=P_a,       X_aX_a^*=R_t,
P_aP_b=0 (a!=b),    sum_a P_a=R_s.                     (WRF4)
```

Consequently

```text
sum_a X_a^*X_a=R_s,
tr_ad(X_a^*X_a)=p^(-2(L+r)),                           (WRF5)
||X_a-X_b||_(HS,ad)^2=2p^(-2(L+r))       (a!=b).       (WRF6)
```

This is not an abstract rank decomposition.  The channels are the literal
Weyl coefficients of the new Heisenberg label factor.  Hence taking all
`p^(2r)` polarized/Pauli return channels, or summing the Gram operators in
the packet orbit of any one of them, reconstructs the larger source
commutant exactly inside the rectangular model.  The exponentially wide
aggregation demanded by the diffuse Schrodinger tower therefore supplies no
strict capacity or density deficit: it is precisely how rectangular escape
stores the lost multiplicity.

There is a sharp positive boundary.  Distinct Weyl channels are orthogonal
and obey `(WRF6)`.  Thus a full-presentation occurrence which authenticates
two distinct indices on one returned payload and forces their channels to
be `epsilon`-close pays the fixed-depth floor

```text
2p^(-2(L+r))<=epsilon^2.                               (WRF7)
```

Absent such a cross-index collision (or a nonsymmetric proper subframe with
an independently paid complement), Parseval aggregation of the compatible
Heisenberg multiplicities cannot prove
`coherent-heisenberg-multiplicity-decoder` or the source-saturated Reynolds
checksum.  Adding all channels merely reaches the sharp `p^(2r)` threshold;
it does not identify one common Leavitt multiplicity reservoir.

DERIVATION
weyl-return-frame-rectangular-proof
