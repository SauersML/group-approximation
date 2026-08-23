---
rg: 2
id: target-saturated-reynolds-return-does-not-lock-leavitt-reservoir
kind: claim
title: A target-saturated Reynolds return does not lock the Leavitt multiplicity reservoir
distinct_from:
  weyl-commutant-superrank-detects-rectangular-return: that computes the two normalized commutant ranks and says that equality of the ranges is impossible; this separates the two inequivalent overlap directions and gives an exact rectangular model saturating the weaker one.
  adjoint-reynolds-return-needs-one-overlap-moment: that gives the general scalar overlap identity for nested packets; this identifies which normalization is necessary in the affine-Leavitt source-to-child orientation and proves that the opposite normalization is vacuous.
  typed-pi-superrank-data-do-not-decode-prescribed-leavitt-carrier: that constructs the complete typed rectangular counterpacket; this extracts its exact returned-Reynolds geometry and the smallest scalar assertion which that counterpacket fails.
---

**ESTABLISHED FIREWALL.**  Let `p>=2`, let

```text
K=C^p tensor C^p tensor C^k,
```

and let the source Weyl packet act on the first factor while the two-child
packet acts on the first two factors.  Denote by `R_s,R_t` their adjoint
Reynolds projections on `End(K)`.  Thus

```text
Ran(R_s)=I_p tensor M_p tensor M_k,
Ran(R_t)=I_(p^2) tensor M_k,
R_t<=R_s.                                                (TSR1)
```

Normalize the trace on the adjoint Hilbert space of `K`.  Then, independently
of the spectator multiplicity `k`,

```text
c_s=tr_ad(R_s)=p^(-2),
c_t=tr_ad(R_t)=p^(-4).                                  (TSR2)
```

For any unitary adjoint actuator `T` put

```text
Theta_T=tr_ad(R_s T^* R_t T R_s).                       (TSR3)
```

Since `T^*R_tT` is a projection of trace `c_t`,

```text
Theta_T<=c_t,
c_s-Theta_T>=p^(-2)-p^(-4).                             (TSR4)
```

The identity actuator attains equality:

```text
Theta_1=tr_ad(R_sR_tR_s)=c_t.                           (TSR5)
```

Thus the returned **target** Reynolds range can lie completely in the source
Reynolds range while the source retains the full fixed complement
`c_s-c_t`.  This is exactly what happens in the rectangular first Leavitt
cell: the source algebra is `M_p tensor I_(pk)`, the target algebra is
`M_(p^2) tensor I_k`, and the target commutant is a proper subspace of the
source commutant.  All typed source/child Pauli tables and rectangular
Steinberg transports remain exact.  In particular target saturation

```text
Theta_T>=c_t-o(1)                                       (TSR6)
```

does **not** authenticate a common multiplicity reservoir and cannot imply
the relative Leavitt products on the prescribed carrier.

The viable scalar direction is the reverse, source-saturated estimate

```text
Theta_T>=c_s-eta.                                       (TSR7)
```

Combining `(TSR4)` and `(TSR7)` gives the sharp fixed payment

```text
eta>=p^(-2)-p^(-4).                                     (TSR8)
```

After fixed finite-packet normalized-HS exactification the same conclusion
holds with `o(1)` errors.  If `T=Ad(U(w))` for one fixed group word, `(TSR3)`
is a finite average of squared ordinary word traces by the Reynolds
expansion.  This does **not** make `(TSR7)` a viable fixed-word relation:
`canonical-marked-reynolds-return-is-subgroup-intersection` pins that average
in canonical microstates to a quotient-subgroup intersection and hence to
at most `c_t=p^(-4)`.  Thus every fixed word actuator lies on the wrong side
of `(TSR7)` even before taking a matrix limit.

Consequently the source-saturated overlap is the smallest *analytic*
endpoint, but its actuator must be extracted nonlinearly from the finite
matrix coordinates (for example as the polar part of a mixed Gram map).  It
cannot be one fixed evaluated group word or a fixed convex average of such
word checksums.  No equality of physical carriers, mutual bicommutant
reconstruction, or pointwise transport of the packet tables is analytically
needed after such a coordinate actuator is available.

This proves both minimality statements relevant to the Leavitt route:

1. one source-saturated overlap checksum is sufficient to detect the
   rectangular label/multiplicity trade; and
2. the superficially similar target-saturated checksum is exactly satisfied
   by that trade and supplies no same-reservoir information.

The remaining compiler problem is therefore directional.  It must make the
returned *smaller target commutant* cover the larger source commutant up to
word-paid leakage using a matrix-coordinate-derived return.  Merely returning
every target invariant to some source invariant proves only `(TSR6)` and
leaves the countermodel untouched; using one fixed word cannot improve the
overlap because canonical trace fixes its subgroup-intersection value.
